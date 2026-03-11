import re

input_file = "/Users/husseinhiyassat/fractal/Eqratech_Hussein_Hiyassat_Project/tests/test_cv_syalaba.csv"
output_file = "/Users/husseinhiyassat/fractal/Eqratech_Hussein_Hiyassat_Project/tests/test_cv_syalaba_no_last_haraka.csv"

def remove_last_haraka(text: str) -> str:
    return re.sub(r'[\u064B-\u0652\u0670]+(?=\s|$)', '', text)

with open(input_file, "r", encoding="utf-8") as f:
    content = f.read()

content = remove_last_haraka(content)

with open(output_file, "w", encoding="utf-8") as f:
    f.write(content)

print("Done:", output_file)