import Mathlib
import Lemma.Definitions.Def_ModularCurve_CharPReduction
import Lemma.Definitions.Def_ModularCurve_NodeLocalized
import Lemma.Definitions.Def_ModularCurve_LambdaSeries

set_option autoImplicit false

noncomputable section

namespace ModularCurve
namespace LambdaNodeLocalized

open CharPReduction

section Point

variable (N : ℕ) [NeZero N] {L : Type*} [CommRing L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k) (a b : k)

def lambdaEval : MvPolynomial (Fin 2) A →+* LaurentSeries L :=
  MvPolynomial.eval₂Hom (CharPReduction.constSeries A) ![lambdaModC L, lambdaNModC L N]

def lambdaLocalizedAtPoint : Subring (LaurentSeries L) where
  carrier := {f | ∃ r s : MvPolynomial (Fin 2) A,
    NodeLocalized.pointEval A red a b s ≠ 0 ∧ f * lambdaEval N A s = lambdaEval N A r}
  zero_mem' := ⟨0, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, map_zero, zero_mul]⟩
  one_mem' := ⟨1, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, one_mul]⟩
  add_mem' := by
    rintro f g ⟨r, s, hs, hf⟩ ⟨u, t, ht, hg⟩
    refine ⟨r * t + u * s, s * t, by rw [map_mul]; exact mul_ne_zero hs ht, ?_⟩
    rw [map_mul, map_add, map_mul, map_mul]
    calc (f + g) * (lambdaEval N A s * lambdaEval N A t)
        = f * lambdaEval N A s * lambdaEval N A t + g * lambdaEval N A t * lambdaEval N A s := by ring
      _ = lambdaEval N A r * lambdaEval N A t + lambdaEval N A u * lambdaEval N A s := by rw [hf, hg]
  neg_mem' := by
    rintro f ⟨r, s, hs, hf⟩
    exact ⟨-r, s, hs, by rw [neg_mul, hf, map_neg]⟩
  mul_mem' := by
    rintro f g ⟨r, s, hs, hf⟩ ⟨u, t, ht, hg⟩
    refine ⟨r * u, s * t, by rw [map_mul]; exact mul_ne_zero hs ht, ?_⟩
    rw [map_mul, map_mul]
    calc f * g * (lambdaEval N A s * lambdaEval N A t)
        = (f * lambdaEval N A s) * (g * lambdaEval N A t) := by ring
      _ = lambdaEval N A r * lambdaEval N A u := by rw [hf, hg]

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
