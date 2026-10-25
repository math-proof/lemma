/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum
import Def.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part5


section

namespace MetaMathlibExt

open scoped BigOperators

lemma encodeSet_injective_aux (d n : ℕ) [NeZero n] :
    Function.Injective (encodeSet_aux d n) := by
  intro P Q hPQ
  have hPS := P.2.1
  have hnS := P.2.2.1
  have hCS := P.2.2.2
  have hPT := Q.2.1
  have hnT := Q.2.2.1
  have hCT := Q.2.2.2
  set S := P.val with hSdef
  set T := Q.val with hTdef
  have bS : ∀ x ∈ S, ∀ k : Fin d, 0 ≤ x k ∧ x k < (n : ℤ) := by
    intro x hx k
    refine ⟨(hCS k).2 x hx, ?_⟩
    have hb := coord_lt_card_aux d S hPS hCS x hx k
    rw [hnS] at hb
    exact hb
  have bT : ∀ y ∈ T, ∀ k : Fin d, 0 ≤ y k ∧ y k < (n : ℤ) := by
    intro y hy k
    refine ⟨(hCT k).2 y hy, ?_⟩
    have hb := coord_lt_card_aux d T hPT hCT y hy k
    rw [hnT] at hb
    exact hb
  have himg : Finset.image (encodeCell_aux d n) S =
      Finset.image (encodeCell_aux d n) T := hPQ
  have hST : S ⊆ T := by
    intro x hx
    have hmem : encodeCell_aux d n x ∈ Finset.image (encodeCell_aux d n) T := by
      rw [← himg]
      exact Finset.mem_image_of_mem _ hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hmem
    have heq : x = y :=
      encodeCell_eq_of_bounds_aux d n x y (bS x hx) (bT y hy) hyx.symm
    rw [heq]
    exact hy
  have hTS : T ⊆ S := by
    intro y hy
    have hmem : encodeCell_aux d n y ∈ Finset.image (encodeCell_aux d n) S := by
      rw [himg]
      exact Finset.mem_image_of_mem _ hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hmem
    have heq : y = x :=
      encodeCell_eq_of_bounds_aux d n y x (bT y hy) (bS x hx) hxy.symm
    rw [heq]
    exact hx
  have hSTeq : S = T := Finset.Subset.antisymm hST hTS
  exact Subtype.ext hSTeq

end MetaMathlibExt
end
