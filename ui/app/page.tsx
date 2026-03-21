"use client";

import { useState } from "react";
import { useAnalyzeStream } from "@/lib/useAnalyzeStream";

type Msg = { role: "user"; content: string };

type ResultTab = "l11" | "l17";

/** إن وُجدت "إنني أفكر" أو "انني افكر" في البداية، تُستأصل لتحليل الجملة فقط */
function sentenceToAnalyze(text: string): string {
  const t = text.trim();
  if (!t) return t;
  const normalized = t
    .slice(0, 80)
    .replace(/\u0625/g, "\u0627")
    .replace(/\u0623/g, "\u0627");
  const prefix = "انني افكر";
  if (normalized.startsWith(prefix)) {
    return t.slice(prefix.length).replace(/^\s+/, "").trim() || t;
  }
  return t;
}

export default function Home() {
  const [input, setInput] = useState("");
  const [messages, setMessages] = useState<Msg[]>([]);
  const [showLogs, setShowLogs] = useState(false);
  const [resultTab, setResultTab] = useState<ResultTab>("l11");

  const {
    steps,
    logs,
    finalText,
    l11Markdown,
    l17Markdown,
    summary,
    running,
    error,
    start,
    stop,
  } = useAnalyzeStream();

  const onSend = async () => {
    const raw = input.trim();
    if (!raw) return;

    const sentence = sentenceToAnalyze(raw);
    setMessages((prev) => [...prev, { role: "user", content: raw }]);
    setInput("");

    try {
      await start(sentence);
    } catch (e: unknown) {
      const msg = e instanceof Error ? e.message : String(e);
      console.error("analyze failed", msg);
    }
  };

  const hasLayerResult = Boolean(l11Markdown || l17Markdown || finalText);

  return (
    <main className="min-h-screen bg-slate-100 text-slate-900" dir="rtl" lang="ar">
      <div className="mx-auto grid max-w-6xl grid-cols-1 gap-4 p-4 lg:grid-cols-[1fr_360px]">
        {/* Chat */}
        <section className="rounded-xl border border-slate-200 bg-white p-5 shadow-sm">
          <div className="mb-4 flex items-center justify-between">
            <h1 className="text-3xl font-semibold text-slate-900">واجهة تحليل الجملة</h1>
            <div className="text-base text-slate-500">Local pipeline via Python</div>
          </div>

          <div className="h-[60vh] overflow-auto rounded-lg border border-slate-200 bg-slate-50/80 p-4">
            {messages.length === 0 && !hasLayerResult && !running ? (
              <div className="text-base text-slate-600">
                اكتب الجملة أو النص المراد تحليله ثم اضغط إرسال.
              </div>
            ) : (
              <div className="space-y-4">
                {messages.map((m, idx) => (
                  <div key={idx} className="text-right">
                    <div
                      className={[
                        "inline-block max-w-[92%] rounded-2xl px-4 py-3 leading-relaxed",
                        "border border-slate-300 bg-slate-200/90 text-slate-900 text-lg",
                      ].join(" ")}
                    >
                      <pre className="whitespace-pre-wrap font-sans text-right">{m.content}</pre>
                    </div>
                  </div>
                ))}

                {running && (
                  <div className="text-right text-base text-slate-500">جاري التحليل…</div>
                )}

                {error && (
                  <div className="rounded-lg border border-red-200 bg-red-50 px-4 py-3 text-right text-base text-red-800">
                    {error}
                  </div>
                )}

                {hasLayerResult && !running && (
                  <div className="rounded-xl border border-slate-200 bg-white p-4 shadow-sm">
                    <div className="mb-3 flex flex-wrap gap-2 border-b border-slate-200 pb-3">
                      <button
                        type="button"
                        onClick={() => setResultTab("l11")}
                        className={[
                          "rounded-lg px-4 py-2 text-base font-semibold transition-colors",
                          resultTab === "l11"
                            ? "bg-blue-600 text-white"
                            : "bg-slate-100 text-slate-800 hover:bg-slate-200",
                        ].join(" ")}
                      >
                        L11 — الإعراب السطحي
                      </button>
                      <button
                        type="button"
                        onClick={() => setResultTab("l17")}
                        className={[
                          "rounded-lg px-4 py-2 text-base font-semibold transition-colors",
                          resultTab === "l17"
                            ? "bg-blue-600 text-white"
                            : "bg-slate-100 text-slate-800 hover:bg-slate-200",
                        ].join(" ")}
                      >
                        الطبقة الجديدة (L17)
                      </button>
                    </div>
                    <pre className="max-h-[42vh] overflow-y-auto whitespace-pre-wrap font-sans text-right text-base leading-relaxed text-slate-900">
                      {resultTab === "l11"
                        ? l11Markdown || "_(لا يوجد محتوى L11)_"
                        : l17Markdown || "_(لا يوجد محتوى L17)_"}
                    </pre>
                    {summary && (
                      <div className="mt-3 border-t border-slate-100 pt-3 text-sm text-slate-600">
                        صلاحية: {String(summary.validity)} · ثقة: {String(summary.confidence)} · نوع الجملة:{" "}
                        {String(summary.sentenceType)}
                      </div>
                    )}
                    <details className="mt-4 rounded-lg border border-slate-100 bg-slate-50/80 p-3 text-right">
                      <summary className="cursor-pointer text-base font-medium text-slate-700">
                        عرض التقرير الكامل (نصّي)
                      </summary>
                      <pre className="mt-2 max-h-[30vh] overflow-y-auto whitespace-pre-wrap font-sans text-sm text-slate-800">
                        {finalText || "—"}
                      </pre>
                    </details>
                  </div>
                )}
              </div>
            )}
          </div>

          <div className="mt-4 flex gap-3">
            <input
              className="w-full rounded-lg border border-slate-300 bg-white px-4 py-3 text-lg outline-none focus:border-blue-500 focus:ring-2 focus:ring-blue-500/20"
              value={input}
              onChange={(e) => setInput(e.target.value)}
              placeholder="اكتب الجملة أو النص المراد تحليله..."
              onKeyDown={(e) => {
                if (e.key === "Enter" && !e.shiftKey) {
                  e.preventDefault();
                  void onSend();
                }
              }}
            />
            {!running ? (
              <button
                onClick={() => void onSend()}
                className="rounded-lg bg-blue-600 px-5 py-3 text-lg font-semibold text-white shadow-sm hover:bg-blue-700"
              >
                إرسال
              </button>
            ) : (
              <button
                onClick={stop}
                className="rounded-lg bg-red-500 px-5 py-3 text-lg font-semibold text-white shadow-sm hover:bg-red-600"
              >
                إيقاف
              </button>
            )}
          </div>

        </section>

        {/* Steps panel */}
        {(running || steps.length > 0) && (
          <aside className="rounded-xl border border-slate-200 bg-white p-5 shadow-md">
            <div className="mb-4 flex items-center justify-between">
              <h2 className="text-2xl font-semibold text-slate-900">خطوات التنفيذ</h2>
              <button
                className="rounded-md border border-slate-300 bg-slate-50 px-3 py-2 text-base font-medium text-slate-700 hover:bg-slate-100"
                onClick={() => setShowLogs((v) => !v)}
              >
                {showLogs ? "إخفاء السجل" : "عرض السجل"}
              </button>
            </div>

            <ol className="space-y-3">
              {steps.map((s) => (
                <li key={s.id} className="rounded-lg border border-slate-200 bg-slate-50/50 p-3">
                  <div className="flex items-center justify-between gap-3">
                    <div className="text-lg text-slate-800">{s.title}</div>
                    <span
                      className={[
                        "rounded-full px-2.5 py-1 text-sm font-medium",
                        s.status === "queued" && "bg-slate-200 text-slate-700",
                        s.status === "running" && "bg-blue-100 text-blue-800",
                        s.status === "done" && "bg-emerald-100 text-emerald-800",
                        s.status === "error" && "bg-red-100 text-red-800",
                      ]
                        .filter(Boolean)
                        .join(" ")}
                    >
                      {s.status}
                    </span>
                  </div>
                  {s.detail && <div className="mt-1.5 text-base text-slate-500">{s.detail}</div>}
                </li>
              ))}
            </ol>

            {showLogs && (
              <div className="mt-4">
                <div className="mb-1.5 text-base text-slate-500">سجل التنفيذ (stdout/stderr)</div>
                <pre
                  dir="ltr"
                  className="h-[30vh] overflow-auto rounded-lg border border-slate-200 bg-slate-900 p-3 text-base leading-7 text-slate-200"
                >
                  {logs || "(لا يوجد سجل بعد)"}
                </pre>
              </div>
            )}
          </aside>
        )}
      </div>
    </main>
  );
}