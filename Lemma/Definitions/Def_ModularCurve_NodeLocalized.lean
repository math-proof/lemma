import Mathlib
import Lemma.Definitions.Def_ModularCurve_CharPReduction

set_option autoImplicit false

noncomputable section

namespace ModularCurve
namespace NodeLocalized

open CharPReduction

section Point

variable (N : ℕ) [NeZero N] {L : Type*} [CommRing L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k) (a b : k)

def modularEval : MvPolynomial (Fin 2) A →+* LaurentSeries L :=
  MvPolynomial.eval₂Hom (CharPReduction.constSeries A) ![jqModC L, jqNModC L N]

def pointEval : MvPolynomial (Fin 2) A →+* k :=
  MvPolynomial.eval₂Hom red ![a, b]

def modularLocalizedAtPoint : Subring (LaurentSeries L) where
  carrier := {f | ∃ r s : MvPolynomial (Fin 2) A, pointEval A red a b s ≠ 0 ∧ f * modularEval N A s = modularEval N A r}
  zero_mem' := ⟨0, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, map_zero, zero_mul]⟩
  one_mem' := ⟨1, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, one_mul]⟩
  add_mem' := by
    rintro f g ⟨r, s, hs, hf⟩ ⟨u, t, ht, hg⟩
    refine ⟨r * t + u * s, s * t, by rw [map_mul]; exact mul_ne_zero hs ht, ?_⟩
    rw [map_mul, map_add, map_mul, map_mul]
    calc (f + g) * (modularEval N A s * modularEval N A t)
        = f * modularEval N A s * modularEval N A t + g * modularEval N A t * modularEval N A s := by ring
      _ = modularEval N A r * modularEval N A t + modularEval N A u * modularEval N A s := by rw [hf, hg]
  neg_mem' := by
    rintro f ⟨r, s, hs, hf⟩
    exact ⟨-r, s, hs, by rw [neg_mul, hf, map_neg]⟩
  mul_mem' := by
    rintro f g ⟨r, s, hs, hf⟩ ⟨u, t, ht, hg⟩
    refine ⟨r * u, s * t, by rw [map_mul]; exact mul_ne_zero hs ht, ?_⟩
    rw [map_mul, map_mul]
    calc f * g * (modularEval N A s * modularEval N A t)
        = (f * modularEval N A s) * (g * modularEval N A t) := by ring
      _ = modularEval N A r * modularEval N A u := by rw [hf, hg]

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
