import Mathlib
import Lemma.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Lemma.Definitions.Def_ModularCurve_JqCoeff

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

def weightFloor (m : ℕ) (w : Place K ↥(modularFunctionFieldC K N)) : ℤ :=
  (if 0 < w.ord (⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N))
      then (2 * (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N))) / 3 else 0)
  + (if 0 < w.ord ((⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N)) - algebraMap K _ 1728)
      then ((m : ℤ) * w.ord ((⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N)) - algebraMap K _ 1728)) / 2
      else 0)
  + (if w.ord (⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N)) < 0
      then (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N)) else 0)

open scoped Classical in

def weightDivisor (m : ℕ) : Divisor K ↥(modularFunctionFieldC K N) :=
  if h : ∃ D : Divisor K ↥(modularFunctionFieldC K N), ∀ w, D w = weightFloor K N m w then h.choose else 0

theorem weightDivisor_apply (m : ℕ)
    (h : ∃ D : Divisor K ↥(modularFunctionFieldC K N), ∀ w, D w = weightFloor K N m w)
    (w : Place K ↥(modularFunctionFieldC K N)) :
    weightDivisor K N m w = weightFloor K N m w := by
  classical
  rw [weightDivisor, dif_pos h]
  exact h.choose_spec w

end ModularCurve

end
