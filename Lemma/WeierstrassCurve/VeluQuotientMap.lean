import Mathlib
import Lemma.WeierstrassCurve.Velu
import Def.WeierstrassCurve_VeluQuotientMap
import Structure.WeierstrassCurve_VeluQuotientMap

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)


lemma IsOddVeluSet.isVeluSet {S : Finset (R × R)} (h : W.IsOddVeluSet S) : W.IsVeluSet S :=
  ⟨h.equation⟩

lemma isOddVeluSet_empty : W.IsOddVeluSet ∅ where
  equation := by simp
  gy_ne_zero := by simp
  x_injOn := by simp

lemma isOddVeluSet_singleton {x y : R} (h : W.toAffine.Equation x y)
    (h2 : W.veluGy x y ≠ 0) : W.IsOddVeluSet {(x, y)} where
  equation := by simpa using h
  gy_ne_zero := by simpa using h2
  x_injOn := by simp

lemma veluQuotient_singleton_negY (x y : R) :
    W.veluQuotient {(x, W.toAffine.negY x y)} = W.veluQuotient {(x, y)} := by
  have ht : W.veluTSum {(x, W.toAffine.negY x y)} = W.veluTSum {(x, y)} := by
    simp only [veluTSum, Finset.sum_singleton]
    exact W.veluT_negY x y
  have hw : W.veluWSum {(x, W.toAffine.negY x y)} = W.veluWSum {(x, y)} := by
    simp only [veluWSum, Finset.sum_singleton]
    exact W.veluW_negY x y
  ext <;> simp only [veluQuotient_a₁, veluQuotient_a₂, veluQuotient_a₃, veluQuotient_a₄,
    veluQuotient_a₆, ht, hw]

section QuotientMap

variable {F : Type*} [Field F] (W : WeierstrassCurve F)


@[simp] lemma veluX_empty (x : F) : W.veluX ∅ x = x := by simp [veluX]

lemma veluX_def_of_ne (S : Finset (F × F)) {x : F} (hx : ∀ Q ∈ S, x ≠ Q.1) :
    W.veluX S x = x + ∑ Q ∈ S, (W.veluT Q.1 Q.2 * (x - Q.1) + W.veluU Q.1 Q.2)
      / (x - Q.1) ^ 2 := by
  unfold veluX
  congr 1
  refine Finset.sum_congr rfl fun Q hQ => ?_
  have h0 : x - Q.1 ≠ 0 := sub_ne_zero.mpr (hx Q hQ)
  field_simp

end QuotientMap

lemma veluQuotient_Δ (S : Finset (R × R)) :
    (W.veluQuotient S).Δ = W.Δ +
      (W.b₂ ^ 4 * W.veluTSum S + 7 * W.b₂ ^ 3 * W.veluWSum S
        - 41 * W.b₂ ^ 2 * W.b₄ * W.veluTSum S - 47 * W.b₂ ^ 2 * W.veluTSum S ^ 2
        - 252 * W.b₂ * W.b₄ * W.veluWSum S + 126 * W.b₂ * W.b₆ * W.veluTSum S
        - 3528 * W.b₂ * W.veluTSum S * W.veluWSum S + 240 * W.b₄ ^ 2 * W.veluTSum S
        - 2400 * W.b₄ * W.veluTSum S ^ 2 + 1512 * W.b₆ * W.veluWSum S
        + 8000 * W.veluTSum S ^ 3 - 21168 * W.veluWSum S ^ 2) := by
  simp only [Δ, veluQuotient_b₂, veluQuotient_b₄, veluQuotient_b₆, veluQuotient_b₈]
  ring

end WeierstrassCurve
