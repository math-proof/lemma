import Mathlib
import Lemma.ModularCurve.CharPReduction
import Lemma.ModularCurve.NodeLocalized
import Lemma.ModularCurve.LambdaSeries
import Def.ModularCurve_LambdaNodeLocalized

set_option autoImplicit false

noncomputable section

namespace ModularCurve
namespace LambdaNodeLocalized

open CharPReduction

section Point

variable (N : ℕ) [NeZero N] {L : Type*} [CommRing L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k) (a b : k)


theorem mem_lambdaLocalizedAtPoint {f : LaurentSeries L} :
    f ∈ lambdaLocalizedAtPoint N A red a b ↔
      ∃ r s : MvPolynomial (Fin 2) A,
        NodeLocalized.pointEval A red a b s ≠ 0 ∧ f * lambdaEval N A s = lambdaEval N A r :=
  Iff.rfl

theorem lambdaEval_mem_lambdaLocalizedAtPoint (p : MvPolynomial (Fin 2) A) :
    lambdaEval N A p ∈ lambdaLocalizedAtPoint N A red a b :=
  ⟨p, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one]⟩

end Point

end LambdaNodeLocalized

end ModularCurve

end
