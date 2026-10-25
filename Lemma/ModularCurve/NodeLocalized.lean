import Mathlib
import Lemma.ModularCurve.CharPReduction
import Def.ModularCurve_NodeLocalized

set_option autoImplicit false

noncomputable section

namespace ModularCurve
namespace NodeLocalized

open CharPReduction

section Point

variable (N : ℕ) [NeZero N] {L : Type*} [CommRing L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k) (a b : k)


theorem mem_modularLocalizedAtPoint {f : LaurentSeries L} :
    f ∈ modularLocalizedAtPoint N A red a b ↔
      ∃ r s : MvPolynomial (Fin 2) A, pointEval A red a b s ≠ 0 ∧ f * modularEval N A s = modularEval N A r :=
  Iff.rfl

theorem modularEval_mem_modularLocalizedAtPoint (p : MvPolynomial (Fin 2) A) :
    modularEval N A p ∈ modularLocalizedAtPoint N A red a b :=
  ⟨p, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one]⟩

end Point

end NodeLocalized

end ModularCurve

end
