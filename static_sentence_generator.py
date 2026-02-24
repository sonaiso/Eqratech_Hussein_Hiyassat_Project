from engines.generation.static_sentence_generator import StaticSentenceGenerator  # noqa: F401

# الاستخدام المباشر
if __name__ == "__main__":
    print("🚀 بدء مولد الجمل العربية الشامل...")
    generator = StaticSentenceGenerator()
    success = generator.save_comprehensive_excel("comprehensive_arabic_grammar.xlsx")

    if success:
        print("\n🎉 تم إكمال توليد الجمل الشاملة بنجاح!")
    else:
        print("\n💥 فشل في إكمال التوليد!")
