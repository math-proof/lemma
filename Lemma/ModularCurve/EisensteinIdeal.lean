import Mathlib
import Def.HeckeGalois_EichlerShimura
import Def.ModularCurve_EisensteinIdeal

set_option autoImplicit false

noncomputable section

namespace ModularCurve


@[simp] lemma eisensteinEval_heckeGen (N : ℕ) (ℓ : Nat.Primes) :
    eisensteinEval N (heckeGen ℓ) = eisensteinSystem N ℓ := by
  simp [eisensteinEval, heckeGen]


lemma mem_eisensteinMaximalIdeal_iff (N p : ℕ) (t : HeckeAlg) :
    t ∈ eisensteinMaximalIdeal N p ↔ (p : ℤ) ∣ eisensteinEval N t := by
  rw [eisensteinMaximalIdeal, Ideal.mem_comap, Ideal.mem_span_singleton]

lemma natCast_mem_eisensteinMaximalIdeal (N p : ℕ) :
    (p : HeckeAlg) ∈ eisensteinMaximalIdeal N p := by
  rw [mem_eisensteinMaximalIdeal_iff, map_natCast]


@[simp] lemma modSystem_apply (m : ℕ) (a : Nat.Primes → ℤ) (ℓ : Nat.Primes) :
    modSystem m a ℓ = (a ℓ : ZMod m) := rfl

end ModularCurve

end
