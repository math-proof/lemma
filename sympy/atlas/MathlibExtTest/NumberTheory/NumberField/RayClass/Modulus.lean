/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/RayClass/Modulus.lean -/

import sympy.atlas.NumberTheory.NumberField.RayClass.Modulus
import Lemma.Nat.NumberField.RayClass.Modulus

@[expose] public noncomputable section

open scoped Classical nonZeroDivisors
open NumberField

namespace N403ModulusTest

variable {K : Type*} [Field K] [NumberField K]

def qPlace : RealPlace ℚ := ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩

example (m : Modulus K) : (1 : Modulus K) * m = m := one_mul m

example (m : Modulus K) : m * (1 : Modulus K) = m := mul_one m

example (v : RealPlace K) : Modulus.infinite v * Modulus.infinite v = Modulus.infinite v :=
  Modulus.infinite_mul_self v

example (m n : Modulus K) :
    (Modulus.gcd m n).infinitePart = m.infinitePart ∩ n.infinitePart := rfl

example (m n : Modulus K) :
    (Modulus.lcm m n).infinitePart = m.infinitePart ∪ n.infinitePart := rfl

example (m : Modulus K) : m ∣ m := by
  rw [Modulus.dvd_unfold]
  exact ⟨le_rfl, fun _ h => h⟩

example : Modulus.infinite qPlace * Modulus.infinite qPlace = Modulus.infinite qPlace :=
  Modulus.infinite_mul_self qPlace

example (m n : Modulus K) :
    ((Modulus.gcd m n).finitePart : Ideal (𝓞 K)) =
      (m.finitePart : Ideal (𝓞 K)) ⊔ (n.finitePart : Ideal (𝓞 K)) :=
  Modulus.gcd_finitePart m n

example (m n : Modulus K) :
    ((Modulus.lcm m n).finitePart : Ideal (𝓞 K)) =
      (m.finitePart : Ideal (𝓞 K)) ⊓ (n.finitePart : Ideal (𝓞 K)) :=
  Modulus.lcm_finitePart m n

example (v : RealPlace K) : (Modulus.infinite v).finitePart = 1 :=
  Modulus.infinite_finitePart v

example (v : RealPlace K) : (Modulus.infinite v).infinitePart = {v} :=
  Modulus.infinite_infinitePart v

end N403ModulusTest
