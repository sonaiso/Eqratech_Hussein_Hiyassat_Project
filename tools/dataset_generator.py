#!/usr/bin/env python3
"""
Dataset Generator for XAI Engine Evaluation Datasets

This tool assists in generating domain-specific samples for Physics, Mathematics,
and Chemistry datasets with proper CTE condition annotations and epistemic levels.

Usage:
    python dataset_generator.py --domain physics --count 100 --output datasets/physics/train.jsonl
    python dataset_generator.py --domain mathematics --count 50 --output datasets/mathematics/validation.jsonl
    python dataset_generator.py --domain chemistry --count 50 --output datasets/chemistry/test.jsonl
"""

import json
import random
import argparse
from typing import List, Dict, Any
from enum import Enum
from datetime import datetime


class Domain(Enum):
    """Scientific domains"""
    PHYSICS = "physics"
    MATHEMATICS = "mathematics"
    CHEMISTRY = "chemistry"


class EpistemicLevel(Enum):
    """Epistemic certainty levels"""
    CERTAIN = "certain"  # يقين
    PROBABLE = "probable"  # ظن
    POSSIBLE = "possible"  # احتمال
    REJECTED = "rejected"  # مرفوض


# Physics Templates
PHYSICS_TEMPLATES = {
    "mechanics": [
        {
            "template": "السرعة تساوي {value} {unit}",
            "unit": "m/s",
            "subdomain": "mechanics",
            "value_range": (1, 100),
            "error_range": (0.0, 0.05)
        },
        {
            "template": "القوة المحصلة = {value} {unit} في اتجاه {direction}",
            "unit": "N",
            "subdomain": "mechanics",
            "value_range": (1, 500),
            "directions": ["الشرق", "الغرب", "الشمال", "الجنوب"],
            "error_range": (0.0, 0.05)
        },
        {
            "template": "العجلة = {value} {unit}",
            "unit": "m/s^2",
            "subdomain": "mechanics",
            "value_range": (0.5, 15),
            "error_range": (0.0, 0.05)
        },
        {
            "template": "الكتلة = {value} {unit}",
            "unit": "kg",
            "subdomain": "mechanics",
            "value_range": (0.1, 1000),
            "error_range": (0.0, 0.10)
        },
    ],
    "thermodynamics": [
        {
            "template": "الضغط = {value} {unit}",
            "unit": "kPa",
            "subdomain": "thermodynamics",
            "value_range": (50, 200),
            "error_range": (0.0, 0.05)
        },
        {
            "template": "درجة الحرارة = {value} {unit}",
            "unit": "°C",
            "subdomain": "thermodynamics",
            "value_range": (-50, 200),
            "error_range": (0.0, 0.10)
        },
        {
            "template": "الحجم = {value} {unit}",
            "unit": "L",
            "subdomain": "thermodynamics",
            "value_range": (0.1, 100),
            "error_range": (0.0, 0.05)
        },
    ],
    "electromagnetism": [
        {
            "template": "التيار الكهربائي = {value} {unit}",
            "unit": "A",
            "subdomain": "electromagnetism",
            "value_range": (0.1, 50),
            "error_range": (0.0, 0.05)
        },
        {
            "template": "الجهد الكهربائي = {value} {unit}",
            "unit": "V",
            "subdomain": "electromagnetism",
            "value_range": (1, 500),
            "error_range": (0.0, 0.05)
        },
        {
            "template": "المقاومة الكهربائية = {value} {unit}",
            "unit": "Ω",
            "subdomain": "electromagnetism",
            "value_range": (0.1, 1000),
            "error_range": (0.0, 0.05)
        },
    ],
    "optics": [
        {
            "template": "الطول الموجي = {value} {unit}",
            "unit": "nm",
            "subdomain": "optics",
            "value_range": (380, 750),
            "error_range": (0.0, 0.03)
        },
        {
            "template": "التردد = {value:.2e} {unit}",
            "unit": "Hz",
            "subdomain": "optics",
            "value_range": (1e12, 1e15),
            "error_range": (0.0, 0.05)
        },
    ]
}

# Mathematics Templates
MATHEMATICS_TEMPLATES = {
    "arithmetic": [
        {
            "template": "{a} + {b} = {c}",
            "subdomain": "arithmetic",
            "operation": "addition"
        },
        {
            "template": "{a} × {b} = {c}",
            "subdomain": "arithmetic",
            "operation": "multiplication"
        },
    ],
    "algebra": [
        {
            "template": "إذا كان x = {value}، فإن {a}x + {b} = {result}",
            "subdomain": "algebra",
            "operation": "linear_equation"
        },
        {
            "template": "x² + {b}x + {c} = 0 له حلان",
            "subdomain": "algebra",
            "operation": "quadratic"
        },
    ],
    "calculus": [
        {
            "template": "d/dx({function}) = {derivative}",
            "subdomain": "calculus",
            "operation": "differentiation"
        },
    ],
    "geometry": [
        {
            "template": "مساحة المستطيل = الطول × العرض = {length} × {width} = {area}",
            "subdomain": "geometry",
            "operation": "area"
        },
    ]
}

# Chemistry Templates
CHEMISTRY_TEMPLATES = {
    "general": [
        {
            "template": "{reactant1} + {reactant2} → {product}",
            "subdomain": "general",
            "type": "reaction"
        },
    ],
    "organic": [
        {
            "template": "CH₃COOH + NaOH → CH₃COONa + H₂O",
            "subdomain": "organic",
            "type": "acid_base"
        },
    ],
    "inorganic": [
        {
            "template": "Fe₂O₃ + 3CO → 2Fe + 3CO₂",
            "subdomain": "inorganic",
            "type": "redox"
        },
    ]
}


class DatasetGenerator:
    """Generate domain-specific dataset samples"""
    
    def __init__(self, domain: Domain, seed: int = 42):
        self.domain = domain
        self.seed = seed
        random.seed(seed)
        self.generated_ids = set()
        
    def generate_sample_id(self, domain_prefix: str, split: str, index: int) -> str:
        """Generate unique sample ID"""
        base_id = f"{domain_prefix}_{split}_{index:03d}"
        # Ensure uniqueness
        counter = 0
        unique_id = base_id
        while unique_id in self.generated_ids:
            counter += 1
            unique_id = f"{base_id}_{counter}"
        self.generated_ids.add(unique_id)
        return unique_id
    
    def choose_epistemic_level(self) -> tuple:
        """Choose epistemic level with target distribution"""
        rand = random.random()
        if rand < 0.65:  # 65% certain
            return EpistemicLevel.CERTAIN, 0.0
        elif rand < 0.85:  # 20% probable
            return EpistemicLevel.PROBABLE, random.uniform(0.03, 0.08)
        elif rand < 0.95:  # 10% possible
            return EpistemicLevel.POSSIBLE, random.uniform(0.08, 0.15)
        else:  # 5% rejected
            return EpistemicLevel.REJECTED, random.uniform(0.15, 0.30)
    
    def generate_physics_sample(self, index: int, split: str = "train") -> Dict[str, Any]:
        """Generate a physics sample"""
        # Choose subdomain
        subdomain = random.choice(list(PHYSICS_TEMPLATES.keys()))
        template_data = random.choice(PHYSICS_TEMPLATES[subdomain])
        
        # Generate values
        value = round(random.uniform(*template_data["value_range"]), 2)
        unit = template_data["unit"]
        
        # Choose epistemic level
        level, error = self.choose_epistemic_level()
        
        # Fill template
        text = template_data["template"].format(
            value=value,
            unit=unit,
            direction=random.choice(template_data.get("directions", [""])) if "directions" in template_data else ""
        ).strip()
        
        # Generate CTE conditions
        cte_conditions = {
            "no_measurement_error": error <= 0.05,
            "no_unit_ambiguity": True,
            "no_experimental_contradiction": True,
            "no_observer_dependence": True,
            "no_scale_violation": True
        }
        
        # Adjust for epistemic level
        if level != EpistemicLevel.CERTAIN:
            cte_conditions["no_measurement_error"] = False
            if level == EpistemicLevel.REJECTED:
                cte_conditions["no_experimental_contradiction"] = False
        
        # Create sample
        sample = {
            "id": self.generate_sample_id("phys", split, index),
            "text": text,
            "subdomain": subdomain,
            "measurement": {
                "value": value,
                "unit": unit,
                "error_margin": error
            },
            "cte_conditions": cte_conditions,
            "epistemic_level": level.value,
            "explanation": self._generate_explanation(subdomain, level, error),
            "generated": True,
            "generation_date": datetime.now().isoformat()
        }
        
        return sample
    
    def generate_mathematics_sample(self, index: int, split: str = "train") -> Dict[str, Any]:
        """Generate a mathematics sample"""
        subdomain = random.choice(list(MATHEMATICS_TEMPLATES.keys()))
        template_data = random.choice(MATHEMATICS_TEMPLATES[subdomain])
        
        # Generate values based on operation
        if subdomain == "arithmetic":
            a = random.randint(1, 100)
            b = random.randint(1, 100)
            if template_data["operation"] == "addition":
                c = a + b
                text = f"{a} + {b} = {c}"
            else:
                c = a * b
                text = f"{a} × {b} = {c}"
        elif subdomain == "algebra":
            a = random.randint(1, 10)
            b = random.randint(1, 20)
            value = random.randint(1, 10)
            result = a * value + b
            text = f"إذا كان x = {value}، فإن {a}x + {b} = {result}"
        else:
            text = template_data["template"]
        
        level, _ = self.choose_epistemic_level()
        
        cte_conditions = {
            "no_axiom_violation": level != EpistemicLevel.REJECTED,
            "no_proof_gap": level in [EpistemicLevel.CERTAIN, EpistemicLevel.PROBABLE],
            "no_domain_restriction": True,
            "no_notation_ambiguity": True,
            "no_computational_error": level != EpistemicLevel.REJECTED
        }
        
        sample = {
            "id": self.generate_sample_id("math", split, index),
            "text": text,
            "subdomain": subdomain,
            "cte_conditions": cte_conditions,
            "epistemic_level": level.value,
            "explanation": self._generate_explanation(subdomain, level, 0.0),
            "generated": True,
            "generation_date": datetime.now().isoformat()
        }
        
        return sample
    
    def generate_chemistry_sample(self, index: int, split: str = "train") -> Dict[str, Any]:
        """Generate a chemistry sample"""
        subdomain = random.choice(list(CHEMISTRY_TEMPLATES.keys()))
        template_data = random.choice(CHEMISTRY_TEMPLATES[subdomain])
        
        text = template_data["template"]
        level, _ = self.choose_epistemic_level()
        
        cte_conditions = {
            "no_stoichiometry_error": level != EpistemicLevel.REJECTED,
            "no_condition_violation": level in [EpistemicLevel.CERTAIN, EpistemicLevel.PROBABLE],
            "no_thermodynamic_impossibility": level != EpistemicLevel.REJECTED,
            "no_mechanism_ambiguity": level != EpistemicLevel.POSSIBLE,
            "no_phase_ambiguity": True
        }
        
        sample = {
            "id": self.generate_sample_id("chem", split, index),
            "text": text,
            "subdomain": subdomain,
            "cte_conditions": cte_conditions,
            "epistemic_level": level.value,
            "explanation": self._generate_explanation(subdomain, level, 0.0),
            "generated": True,
            "generation_date": datetime.now().isoformat()
        }
        
        return sample
    
    def _generate_explanation(self, subdomain: str, level: EpistemicLevel, error: float) -> str:
        """Generate explanation based on epistemic level"""
        if level == EpistemicLevel.CERTAIN:
            return f"قياس دقيق في مجال {subdomain}"
        elif level == EpistemicLevel.PROBABLE:
            return f"قياس تقريبي ({error*100:.1f}% خطأ) في مجال {subdomain}"
        elif level == EpistemicLevel.POSSIBLE:
            return f"تقدير ({error*100:.1f}% خطأ) في مجال {subdomain}"
        else:
            return f"قيمة مرفوضة في مجال {subdomain}"
    
    def generate_samples(self, count: int, split: str = "train") -> List[Dict[str, Any]]:
        """Generate multiple samples"""
        samples = []
        for i in range(count):
            if self.domain == Domain.PHYSICS:
                sample = self.generate_physics_sample(i + 1, split)
            elif self.domain == Domain.MATHEMATICS:
                sample = self.generate_mathematics_sample(i + 1, split)
            elif self.domain == Domain.CHEMISTRY:
                sample = self.generate_chemistry_sample(i + 1, split)
            else:
                raise ValueError(f"Unknown domain: {self.domain}")
            samples.append(sample)
        return samples
    
    def save_to_jsonl(self, samples: List[Dict[str, Any]], output_path: str):
        """Save samples to JSONL file"""
        with open(output_path, 'a', encoding='utf-8') as f:
            for sample in samples:
                f.write(json.dumps(sample, ensure_ascii=False) + '\n')
        print(f"✅ Saved {len(samples)} samples to {output_path}")


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(description="Generate dataset samples for XAI Engine evaluation")
    parser.add_argument("--domain", required=True, choices=["physics", "mathematics", "chemistry"],
                        help="Scientific domain")
    parser.add_argument("--count", type=int, required=True, help="Number of samples to generate")
    parser.add_argument("--split", default="train", choices=["train", "validation", "test"],
                        help="Dataset split")
    parser.add_argument("--output", required=True, help="Output JSONL file path")
    parser.add_argument("--seed", type=int, default=42, help="Random seed for reproducibility")
    parser.add_argument("--append", action="store_true", help="Append to existing file")
    
    args = parser.parse_args()
    
    # Create generator
    domain = Domain(args.domain)
    generator = DatasetGenerator(domain, seed=args.seed)
    
    print(f"🚀 Generating {args.count} {args.domain} samples for {args.split} split...")
    
    # Clear file if not appending
    if not args.append:
        with open(args.output, 'w', encoding='utf-8') as f:
            pass
    
    # Generate samples
    samples = generator.generate_samples(args.count, args.split)
    
    # Save to file
    generator.save_to_jsonl(samples, args.output)
    
    # Print statistics
    levels = {}
    for sample in samples:
        level = sample["epistemic_level"]
        levels[level] = levels.get(level, 0) + 1
    
    print(f"\n📊 Epistemic Level Distribution:")
    for level, count in sorted(levels.items()):
        print(f"  {level}: {count} ({count/len(samples)*100:.1f}%)")
    
    print(f"\n✅ Dataset generation complete!")
    print(f"📁 Output: {args.output}")
    print(f"📈 Total samples: {len(samples)}")


if __name__ == "__main__":
    main()
