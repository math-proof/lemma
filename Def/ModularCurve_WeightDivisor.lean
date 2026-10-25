import Mathlib
import Class.AlgebraicCurve_DivisorClassGroup
import Def.ModularCurve_JqCoeff

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

end ModularCurve

end
