import { NextRequest } from "next/server";
import { spawn } from "node:child_process";
import { randomUUID } from "node:crypto";
import fs from "node:fs/promises";
import path from "node:path";
import os from "node:os";
import type { ErqaMatch } from "../../../lib/erqaLookup";
import { buildDirectPipelineUiPayload } from "../../../lib/directAnalysisSynthesis";
import {
  buildErqaFinalReportArabic,
  buildErqaL17StyleMarkdown,
  buildErqaWordLines,
  findErqaMatch,
  loadErqaRows,
  normalizeArabicText,
  tokenizeNormalized,
} from "../../../lib/erqaLookup";

export const runtime = "nodejs";
export const dynamic = "force-dynamic";

type StepStatus = "queued" | "running" | "done" | "error";

function sseEvent(event: string, data: unknown) {
  return `event: ${event}\ndata: ${JSON.stringify(data)}\n\n`;
}

function summarizePipeline(pipeline: any) {
  const lo = pipeline?.layer_outputs ?? {};
  const fv = pipeline?.final_validation ?? {};

  const tr8 = lo?.L8_ROOT_EXTRACTION?.transformation_result ?? {};
  const tr9 = lo?.L9_WAZN_MATCHING?.transformation_result ?? {};
  const tr11 = lo?.L11_I3RAB?.transformation_result ?? {};
  const tr12 = lo?.L12_SEMANTIC_RHETORICAL?.transformation_result ?? {};

  const words8: any[] = tr8?.words ?? [];
  const words9: any[] = tr9?.words ?? [];
  const tokenResults: any[] = tr11?.token_results ?? [];

  const rootsFound = words8.filter((w) => w?.root).length;
  const waznFound = words9.filter((w) => w?.template || w?.word_wazn).length;
  const i3rabFound = tokenResults.filter((t) => (t?.i3rab_text ?? "").trim()).length;

  const validity = fv?.global_validity ?? "—";
  const confidence = fv?.final_confidence ?? "—";
  const sentenceType = tr12?.sentence_type ?? "—";

  return { validity, confidence, sentenceType, rootsFound, waznFound, i3rabFound };
}

export async function POST(req: NextRequest) {
  const body = await req.json().catch(() => ({}));
  const text: string = (body?.text ?? "").toString().trim();
  const render: string = (body?.render ?? "detailed").toString();

  if (!text) return new Response("Missing text", { status: 400 });

  const encoder = new TextEncoder();

  // IMPORTANT: app is in ui/, pipeline repo root is one level up
  const repoRoot = path.resolve(process.cwd(), "..");

  let erqaMatch: ErqaMatch | null = null;
  try {
    const rows = await loadErqaRows(repoRoot);
    const toks = tokenizeNormalized(normalizeArabicText(text));
    erqaMatch = findErqaMatch(rows, toks);
  } catch (e) {
    console.error("[analyze] ERQA lookup skipped:", e);
  }

  const tmpId = randomUUID();
  const jsonPath = path.join(os.tmpdir(), `pipeline_${tmpId}.json`);

  const stream = new ReadableStream<Uint8Array>({
    start(controller) {
      const write = (event: string, data: unknown) => {
        controller.enqueue(encoder.encode(sseEvent(event, data)));
      };

      const stepCreated = (id: string, title: string, status: StepStatus) =>
        write("step_created", { id, title, status, ts: Date.now() });

      const stepUpdated = (id: string, status: StepStatus, detail?: string) =>
        write("step_updated", { id, status, detail, ts: Date.now() });

      stepCreated("s0", "تهيئة الطلب", "running");
      if (erqaMatch) {
        stepCreated("s1", "مطابقة النص مع erqa_i3rab.csv", "queued");
        stepCreated("s2", "تنسيق الإعراب المقبول (ERQA)", "queued");
        stepCreated("s3", "إخراج النتيجة النهائية", "queued");
      } else {
        stepCreated("s1", "تشغيل التحليل المحلي (pipeline)", "queued");
        stepCreated("s2", "قراءة JSON وتوليد ملخص", "queued");
        stepCreated("s3", "إخراج النتيجة النهائية", "queued");
      }

      stepUpdated("s0", "done");

      if (erqaMatch) {
        stepUpdated("s1", "done", `سورة ${erqaMatch.surah} ، آية ${erqaMatch.ayah}`);
        stepUpdated("s2", "done");
        stepUpdated("s3", "running");
        const wordI3rabLines = buildErqaWordLines(erqaMatch);
        const l17Markdown = buildErqaL17StyleMarkdown(erqaMatch);
        const finalText = buildErqaFinalReportArabic(erqaMatch);
        write("final", {
          text: finalText,
          summary: {
            validity: "ERQA",
            confidence: "—",
            sentenceType: `سورة ${erqaMatch.surah} ، آية ${erqaMatch.ayah}`,
            rootsFound: 0,
            waznFound: 0,
            i3rabFound: erqaMatch.rows.length,
          },
          l11Markdown: "",
          l11MarkdownFull: "",
          l17Markdown,
          wordI3rabLines,
          analysisSource: "quran_erqa",
          analysisSourceLabel: "Quran Accepted Analysis (ERQA)",
          directDisplayPolicy: "quran_erqa",
          weakL17: false,
          l11Downgraded: false,
          erqaMatch: {
            surah: erqaMatch.surah,
            ayah: erqaMatch.ayah,
            matchKind: erqaMatch.kind,
            startWordIndex: erqaMatch.startWordIndex,
            tokenCount: erqaMatch.rows.length,
          },
        });
        stepUpdated("s3", "done");
        controller.close();
        return;
      }

      stepUpdated("s1", "running");

      const child = spawn(
        "python3",
        [
          "scripts/analyze_sentence.py",
          text,
          "--render",
          render,
          "--no-report",
          "--save-json",
          jsonPath,
        ],
        {
          cwd: repoRoot,
          env: { ...process.env, PYTHONPATH: "src" },
        }
      );

      const onAbort = () => {
        try {
          write("log_delta", { stream: "stderr", text: "\n[UI] Aborted by user\n" });
          child.kill("SIGTERM");
        } catch {}
        controller.close();
      };

      req.signal.addEventListener("abort", onAbort);

      const stdoutChunks: string[] = [];
      child.stdout?.on("data", (c: Buffer) => {
        const s = c.toString("utf-8");
        stdoutChunks.push(s);
        write("log_delta", { stream: "stdout", text: s });
      });
      child.stderr?.on("data", (c: Buffer) =>
        write("log_delta", { stream: "stderr", text: c.toString("utf-8") })
      );

      child.on("error", (err) => {
        stepUpdated("s1", "error", err.message);
        write("error", { message: "Failed to start python process", detail: err.message });
        controller.close();
      });

      child.on("close", async (code) => {
        req.signal.removeEventListener("abort", onAbort);
        if (req.signal.aborted) return;

        if (code !== 0 && code !== null) {
          stepUpdated("s1", "error", `process exit code = ${code}`);
          write("error", { message: `Pipeline failed with exit code ${code}` });
          controller.close();
          return;
        }

        stepUpdated("s1", "done");
        stepUpdated("s2", "running");

        try {
          const raw = await fs.readFile(jsonPath, "utf-8");
          const pipeline = JSON.parse(raw);
          const summary = summarizePipeline(pipeline);

          stepUpdated("s2", "done");
          stepUpdated("s3", "running");

          // نفس مخرجات السكربت: تقرير كامل (SECTIONS 1–8) بدل الملخص فقط
          let fullReport = stdoutChunks.join("");
          fullReport = fullReport.replace(/\n?\[Saved pipeline JSON to[^\n]*\]\n?/g, "\n");
          fullReport = fullReport.replace(/\n?\[Saved report to[^\n]*\]\n?/g, "\n");
          const finalText =
            fullReport.trim() ||
            `ملخص التحليل:\n- الصلاحية: ${summary.validity}\n- الثقة: ${summary.confidence}\n- نوع الجملة: ${summary.sentenceType}\n- عدد الكلمات ذات الجذر: ${summary.rootsFound}\n- عدد الكلمات ذات الوزن: ${summary.waznFound}\n- عدد الكلمات ذات الإعراب: ${summary.i3rabFound}\n`;

          const ui = buildDirectPipelineUiPayload(pipeline);
          write("final", {
            text: finalText,
            summary,
            l11Markdown: ui.l11Markdown,
            l11MarkdownFull: ui.l11MarkdownFull,
            l17Markdown: ui.l17Markdown,
            wordI3rabLines: ui.wordI3rabLines,
            analysisSource: "direct_pipeline",
            analysisSourceLabel: ui.analysisSourceLabel,
            directDisplayPolicy: ui.displayPolicy,
            weakL17: ui.weakL17,
            l11Downgraded: ui.l11Downgraded,
          });
          stepUpdated("s3", "done");
          controller.close();
        } catch (e: any) {
          stepUpdated("s2", "error", e?.message ?? String(e));
          write("error", { message: "Failed to read/parse pipeline JSON", detail: e?.message ?? String(e) });
          controller.close();
        } finally {
          try {
            await fs.unlink(jsonPath);
          } catch {}
        }
      });
    },
  });

  return new Response(stream, {
    headers: {
      "Content-Type": "text/event-stream; charset=utf-8",
      "Cache-Control": "no-cache, no-transform",
      Connection: "keep-alive",
    },
  });
}