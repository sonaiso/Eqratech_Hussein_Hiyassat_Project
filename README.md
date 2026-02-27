# Eqratech Arabic Diana Project
# مشروع إقرأتك للعربية - ديانا

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Python 3.8+](https://img.shields.io/badge/python-3.8+-blue.svg)](https://www.python.org/downloads/)

مشروع Python لمعالجة اللغة العربية الطبيعية مع جميع أدوات الأفعال والأسماء العربية.

Python NLP Project with all Arabic tools, verbs and names.

---

## 📁 Project Structure | هيكل المشروع

```
Eqratech_Arabic_Diana_Project/
├── *_engine.py              # Grammar processing engines (محركات المعالجة)
├── *.csv                    # Data files (ملفات البيانات)
├── run_server.py            # Server runner
├── requirements.txt         # Python dependencies
├── LICENSE                  # MIT License
└── README.md                # This file
```

---

## 🚀 Quick Start | البدء السريع

### Installation | التثبيت

```bash
# Clone the repository
git clone https://github.com/sonaiso/Eqratech_Arabic_Diana_Project.git
cd Eqratech_Arabic_Diana_Project

# Install Python dependencies
pip install -r requirements.txt
```

### Run | التشغيل

```bash
# Run the server
python run_server.py

# Or using uvicorn directly
uvicorn web_app.main:app --reload
```

---

## 📚 Main Components | المكونات الرئيسية

### Grammar Engines | محركات القواعد النحوية

| Engine | Description | الوصف |
|--------|-------------|-------|
| `verbs_engine.py` | Verb processing | محرك الأفعال |
| `phonemes_engine.py` | Phonemes processing | محرك الفونيمات |
| `gender_engine.py` | Grammatical gender | محرك الجنس النحوي |
| `demonstratives_engine.py` | Demonstrative pronouns | محرك أسماء الإشارة |
| `particles_engine.py` | Particles processing | محرك الحروف |

### Morphology Engines | محركات الصرف

| Engine | Description | الوصف |
|--------|-------------|-------|
| `active_participle_engine.py` | Active participle | اسم الفاعل |
| `passive_participle_engine.py` | Passive participle | اسم المفعول |
| `superlative_engine.py` | Superlative forms | أفعل التفضيل |
| `tasgheer_engine.py` | Diminutive forms | التصغير |

### Rhetoric Engines | محركات البلاغة

| Engine | Description | الوصف |
|--------|-------------|-------|
| `tashbih_engine.py` | Simile | التشبيه |
| `istiara_engine.py` | Metaphor | الاستعارة |
| `kinaya_engine.py` | Metonymy | الكناية |
| `tibaq_engine.py` | Antithesis | الطباق |

---

## 🤝 Contributing | المساهمة

Contributions are welcome! Please feel free to submit a Pull Request.

نرحب بالمساهمات! لا تتردد في تقديم طلب سحب (Pull Request).

---

## 📄 License | الرخصة

This project is licensed under the [MIT License](LICENSE).

هذا المشروع مرخص تحت [رخصة MIT](LICENSE).

---

## 📞 Contact | التواصل

For questions and inquiries, please open an Issue in the repository.

للأسئلة والاستفسارات، يرجى فتح Issue في المستودع.
