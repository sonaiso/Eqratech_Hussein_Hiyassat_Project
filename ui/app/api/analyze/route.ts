import { NextRequest } from "next/server";
import { spawn } from "node:child_process";
import { randomUUID } from "node:crypto";
import fs from "node:fs/promises";
import path from "node:path";
import os from "node:os";

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

/** Markdown view of L11 surface iʿrāb (token_results). */
function buildL11Markdown(pipeline: unknown): string {
  const lo = (pipeline as { layer_outputs?: Record<string, unknown> })?.layer_outputs ?? {};
  const tr = (lo.L11_I3RAB as { transformation_result?: { token_results?: unknown[] } })
    ?.transformation_result;
  const tokens = tr?.token_results;
  if (!Array.isArray(tokens) || !tokens.length) {
    return "## L11 — الإعراب السطحي\n\n_(لا توجد نتائج L11 في JSON.)_";
  }
  const lines: string[] = ["## L11 — الإعراب السطحي", ""];
  for (const t of tokens) {
    const row = t as { surface?: string; i3rab_text?: string };
    const surf = (row.surface ?? "").trim();
    const i3 = (row.i3rab_text ?? "").trim();
    if (!surf && !i3) continue;
    lines.push(`- **${surf || "—"}** — ${i3 || "—"}`);
  }
  return lines.join("\n");
}

/** Markdown view of L17 rule-based layer (Batch 2.5+). */
function buildL17Markdown(pipeline: unknown): string {
  const lo = (pipeline as { layer_outputs?: Record<string, unknown> })?.layer_outputs ?? {};
  const l17 = lo.L17_RULE_BASED_I3RAB as
    | { transformation_result?: Record<string, unknown> }
    | undefined;
  const tr = l17?.transformation_result;
  if (!tr) {
    return "## L17 — الإعراب القواعدي\n\n_(طبقة L17 غير موجودة في مخرجات الـ pipeline.)_";
  }
  const lines: string[] = ["## L17 — الإعراب القواعدي (الطبقة الجديدة)", ""];
  const rs = tr.reasoning_summary as
    | { resolved_tokens?: number; candidate_tokens?: number; unresolved_tokens?: number }
    | undefined;
  if (rs) {
    lines.push(
      `**ملخص:** محلول: ${rs.resolved_tokens ?? "—"} | مرشح: ${rs.candidate_tokens ?? "—"} | غير محلول: ${rs.unresolved_tokens ?? "—"}`,
      ""
    );
  }
  const tokenReasoning = tr.token_reasoning as Array<Record<string, unknown>> | undefined;
  if (Array.isArray(tokenReasoning) && tokenReasoning.length) {
    for (const row of tokenReasoning) {
      const surf = String(row.surface ?? "").trim();
      const role = String(row.syntactic_role ?? "").trim();
      const i3 = String(row.i3rab_case_or_mood ?? "").trim();
      const marker = String(row.marker ?? "").trim();
      const status = String(row.status ?? "").trim();
      const steps = row.reasoning_steps;
      const stepStr = Array.isArray(steps) ? (steps as string[]).join(" ← ") : "";
      lines.push(`### ${surf || "—"}`);
      lines.push(`- **الوظيفة:** ${role || "—"}`);
      lines.push(`- **الإعراب / الصيغة:** ${i3 || "—"}`);
      if (marker && marker !== "—") lines.push(`- **العلامة:** ${marker}`);
      lines.push(`- **الحالة:** ${status || "—"}`);
      if (stepStr) lines.push(`- **خطوات التعليل:** ${stepStr}`);
      lines.push("");
    }
  } else {
    lines.push("_(لا توجد صفوف token_reasoning.)_", "");
  }
  const kia = tr.khabar_in_analysis;
  if (kia != null && typeof kia === "object" && Object.keys(kia as object).length) {
    lines.push("### تحليل خبر «إن»", "```json", JSON.stringify(kia, null, 2), "```");
  }
  return lines.join("\n").trim();
}

export async function POST(req: NextRequest) {
  const body = await req.json().catch(() => ({}));
  const text: string = (body?.text ?? "").toString().trim();
  const render: string = (body?.render ?? "detailed").toString();

  if (!text) return new Response("Missing text", { status: 400 });

  const encoder = new TextEncoder();

  // IMPORTANT: app is in ui/, pipeline repo root is one level up
  const repoRoot = path.resolve(process.cwd(), "..");

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
      stepCreated("s1", "تشغيل التحليل المحلي (pipeline)", "queued");
      stepCreated("s2", "قراءة JSON وتوليد ملخص", "queued");
      stepCreated("s3", "إخراج النتيجة النهائية", "queued");

      stepUpdated("s0", "done");
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

          const l11Markdown = buildL11Markdown(pipeline);
          const l17Markdown = buildL17Markdown(pipeline);
          write("final", { text: finalText, summary, l11Markdown, l17Markdown });
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