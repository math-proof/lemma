/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/CarrollIdentity.lean -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.LinearCombination
import Def.LinearAlgebra.Matrix.CarrollIdentity


namespace MetaMathlibExt.CarrollIdentity

open Matrix

section

variable {m : ℕ} {S : Type*} [CommRing S] (i j : Fin (m + 2))

lemma carrollSplit_bijective (p q : Fin (m + 2)) (hp : p = i ∨ p = j)
    (hq : q = i ∨ q = j) (hqp : q ≠ p) :
    Function.Bijective (carrollSplit i j p q hp hq hqp) := by
  constructor
  · intro a b hab
    by_cases ha : Fin.succAbove p a = q
    · by_cases hb : Fin.succAbove p b = q
      · exact Fin.succAbove_right_injective (ha.trans hb.symm)
      · simp only [carrollSplit, dif_pos ha, dite_eq_right hb] at hab
        exact absurd hab Sum.inr_ne_inl
    · by_cases hb : Fin.succAbove p b = q
      · simp only [carrollSplit, dite_eq_right ha, dif_pos hb] at hab
        exact absurd hab Sum.inl_ne_inr
      · simp only [carrollSplit, dite_eq_right ha, dite_eq_right hb] at hab
        simp only [Sum.inl.injEq] at hab
        have h2 : Fin.succAbove p a = Fin.succAbove p b :=
          congrArg Subtype.val hab
        exact Fin.succAbove_right_injective h2
  · intro y
    cases y with
    | inl x =>
      have hxp : x.val ≠ p := by
        rcases hp with rfl | rfl
        · exact x.prop.1
        · exact x.prop.2
      obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hxp
      refine ⟨a, ?_⟩
      have hxq : Fin.succAbove p a ≠ q := by
        rw [ha]
        rcases hq with rfl | rfl
        · exact x.prop.1
        · exact x.prop.2
      simp only [carrollSplit, dite_eq_right hxq]
      exact congrArg Sum.inl (Subtype.ext ha)
    | inr k =>
      obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hqp
      refine ⟨a, ?_⟩
      simp only [carrollSplit, dif_pos ha]
      exact congrArg Sum.inr (Subsingleton.elim _ _)

end
end MetaMathlibExt.CarrollIdentity
