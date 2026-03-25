"use client";

import { useEffect, useState } from "react";
import { useAnalyzeStream } from "@/lib/useAnalyzeStream";

type Msg = { role: "user"; content: string };

type ResultTab = "l11" | "l17" | "words";

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
  /** التبويب الثالث: الكلمة والإعراب فقط — يُفتح افتراضياً لتسهيل القراءة */
  const [resultTab, setResultTab] = useState<ResultTab>("words");

  const {
    steps,
    logs,
    finalText,
    l11Markdown,
    l11MarkdownFull,
    l17Markdown,
    wordI3rabLines,
    directDisplayPolicy,
    l11Downgraded,
    summary,
    analysisSource,
    analysisSourceLabel,
    erqaMatch,
    running,
    error,
    start,
    stop,
  } = useAnalyzeStream();

  useEffect(() => {
    if (analysisSource === "quran_erqa" && resultTab === "l11") {
      setResultTab("words");
    }
  }, [analysisSource, resultTab]);

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

  const hasLayerResult = Boolean(l11Markdown || l17Markdown || wordI3rabLines || finalText);

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
                    {analysisSource === "quran_erqa" && (
                      <div
                        className="mb-3 rounded-lg border border-emerald-300 bg-emerald-50 px-4 py-3 text-right text-base text-emerald-950"
                        dir="rtl"
                      >
                        <div className="font-semibold">
                          {analysisSourceLabel || "Quran Accepted Analysis (ERQA)"}
                        </div>
                        {erqaMatch && (
                          <div className="mt-1 text-sm text-emerald-900">
                            سورة {erqaMatch.surah} ، آية {erqaMatch.ayah}
                            {erqaMatch.matchKind === "phrase"
                              ? ` — تطابق عبارة (بداية فهرسة الكلمة ${erqaMatch.startWordIndex})`
                              : " — تطابق آية كاملة"}
                          </div>
                        )}
                        <div className="mt-2 text-sm text-emerald-800">
                          المصدر: <span dir="ltr">data/erqa_i3rab.csv</span> — لم يُشغَّل خط الأنابيب لهذا الطلب.
                        </div>
                        <div className="mt-2 text-sm text-emerald-900/90">
                          الإجابة المعتمدة: تبويب «الكلمة والإعراب» (<span dir="ltr">gold_i3rab</span>) فقط. لا يُعرض
                          طبقة L11 السطحية لأنها غير موثوقة كطبقة تحليل للنص القرآني عند وجود قبول ERQA، ولا نكرر
                          نفس الإعراب في تبويب منفصل باسم L11.
                        </div>
                      </div>
                    )}
                    {analysisSource === "direct_pipeline" && (
                      <div
                        className={[
                          "mb-3 rounded-lg px-4 py-2 text-right text-sm",
                          directDisplayPolicy === "structural_synthesis"
                            ? "border border-amber-200 bg-amber-50 text-amber-950"
                            : "border border-slate-200 bg-slate-50 text-slate-700",
                        ].join(" ")}
                      >
                        {analysisSourceLabel || "Direct Analysis"}
                        {directDisplayPolicy === "structural_synthesis"
                          ? " — الإجابة المعتمدة: «الكلمة والإعراب» (دمج L11B + المرحلة 15). L17 جزئي هنا ويُعرض في تبويبه كمرجع فقط وليس كجواب نهائي. L11 السطحي مُخفّض (مرجع غير موثوق)."
                          : " — مخرجات الأنابيب المحلي (L11 / L17)."}
                      </div>
                    )}
                    <div className="mb-3 flex flex-wrap gap-2 border-b border-slate-200 pb-3">
                      {analysisSource !== "quran_erqa" && (
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
                      )}
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
                        {analysisSource === "quran_erqa"
                          ? "تفاصيل قبول (ثانوي — ليست L17)"
                          : directDisplayPolicy === "structural_synthesis"
                            ? "L17 — مرجع فقط (ليس الجواب النهائي)"
                            : "الطبقة الجديدة (L17)"}
                      </button>
                      <button
                        type="button"
                        onClick={() => setResultTab("words")}
                        className={[
                          "rounded-lg px-4 py-2 text-base font-semibold transition-colors",
                          resultTab === "words"
                            ? "bg-emerald-600 text-white"
                            : "bg-slate-100 text-slate-800 hover:bg-slate-200",
                        ].join(" ")}
                      >
                        الكلمة والإعراب
                      </button>
                    </div>
                    {resultTab === "words" && (
                      <p className="mb-2 text-right text-sm text-slate-600">
                        كل سطر: <span className="font-mono" dir="ltr">الكلمة،الإعراب</span>
                        {analysisSource === "quran_erqa"
                          ? " — المصدر المعتمد الوحيد: gold_i3rab من erqa_i3rab.csv (قبول قرآني)."
                          : directDisplayPolicy === "structural_synthesis"
                            ? " — الجواب المعتمد: L11B + المرحلة 15 أولاً؛ L17 فقط عند كونه فعلاً محلولاً بقوة. L11 النصي لا يُعتمد (يظهر مُوسوماً كمرجع غير موثوق إن وُجد)."
                            : " — من L11 (مثل عمودَي الكلمة والإعراب في الملف الذهبي)."}
                      </p>
                    )}
                    {resultTab === "l17" && analysisSource === "quran_erqa" && (
                      <p className="mb-2 text-right text-sm text-amber-900/90">
                        هذا التبويب لحقول ERQA الثانوية فقط؛ قد يتضمن system_i3rab كمرجع قديم غير موثوق. لا
                        يُستخدم كإجابة نهائية.
                      </p>
                    )}
                    {resultTab === "l17" &&
                      analysisSource === "direct_pipeline" &&
                      directDisplayPolicy === "structural_synthesis" && (
                        <p className="mb-2 text-right text-sm text-amber-900/90">
                          L17 تغطيته جزئية على هذه الجملة؛ ليس المصدر المعتمد للإجابة الكاملة. راجع «الكلمة
                          والإعراب» للدمج مع L11B والمرحلة 15.
                        </p>
                      )}
                    <pre className="max-h-[42vh] overflow-y-auto whitespace-pre-wrap font-sans text-right text-base leading-relaxed text-slate-900">
                      {resultTab === "l11"
                        ? l11Markdown || "_(لا يوجد محتوى L11)_"
                        : resultTab === "l17"
                          ? l17Markdown || "_(لا يوجد محتوى L17)_"
                          : wordI3rabLines || "_(لا يوجد إعراب مبسّط.)_"}
                    </pre>
                    {resultTab === "l11" && l11Downgraded && (l11MarkdownFull || "").trim().length > 0 && (
                      <details className="mt-3 rounded-lg border border-slate-200 bg-slate-50/90 p-3 text-right text-sm text-slate-700">
                        <summary className="cursor-pointer font-medium text-slate-800 hover:text-slate-900">
                          عرض L11 الكامل (النص السطحي)
                        </summary>
                        <pre className="mt-2 max-h-[30vh] overflow-y-auto whitespace-pre-wrap font-sans text-right text-sm leading-relaxed text-slate-900">
                          {l11MarkdownFull}
                        </pre>
                      </details>
                    )}
                    {summary && (
                      <div className="mt-3 border-t border-slate-100 pt-3 text-sm text-slate-600">
                        صلاحية: {String(summary.validity)} · ثقة: {String(summary.confidence)} · نوع الجملة:{" "}
                        {String(summary.sentenceType)}
                      </div>
                    )}
                    <details className="mt-4 rounded-lg border border-slate-100 bg-slate-50/80 p-3 text-right">
                      <summary className="cursor-pointer text-base font-medium text-slate-700">
                        {analysisSource === "quran_erqa"
                          ? "ملخص الطلب (نصّي — بلا تكرار إعراب L11)"
                          : "عرض التقرير الكامل (نصّي)"}
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