/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum
import Def.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part6


section

namespace MetaMathlibExt

open scoped BigOperators

lemma compress_expand_aux2 (d : ℕ) (A : Finset (Fin d))
    (y : latticeCell A.card) :
    compressCell_aux2 d A (expandCell_aux2 d A y) = y := by
  funext i
  simp only [compressCell_aux2, expandCell_aux2]
  have hmem : ((Finset.orderIsoOfFin A rfl i : ↥A).val) ∈ A :=
    (Finset.orderIsoOfFin A rfl i).property
  rw [dite_eq_left hmem]
  have heq : (⟨((Finset.orderIsoOfFin A rfl i : ↥A).val), hmem⟩ : ↥A) =
      Finset.orderIsoOfFin A rfl i := Subtype.ext rfl
  rw [heq, OrderIso.symm_apply_apply]

lemma expand_compress_aux2 (d : ℕ) (A : Finset (Fin d))
    (x : latticeCell d) (hz : ∀ k : Fin d, k ∉ A → x k = 0) :
    expandCell_aux2 d A (compressCell_aux2 d A x) = x := by
  funext k
  simp only [expandCell_aux2, compressCell_aux2]
  by_cases hk : k ∈ A
  · rw [dite_eq_left hk]
    obtain ⟨i, hi⟩ := (Finset.orderIsoOfFin A rfl).surjective ⟨k, hk⟩
    have hsym : (Finset.orderIsoOfFin A rfl).symm ⟨k, hk⟩ = i := by
      rw [← hi]
      exact OrderIso.symm_apply_apply (Finset.orderIsoOfFin A rfl) i
    rw [hsym, hi]
  · rw [dite_eq_right hk, hz k hk]

lemma compress_preserves_adj_aux2 (d : ℕ) (A : Finset (Fin d))
    (x y : latticeCell d)
    (hxz : ∀ k : Fin d, k ∉ A → x k = 0)
    (hyz : ∀ k : Fin d, k ∉ A → y k = 0)
    (h : faceAdjacent d x y) :
    faceAdjacent A.card (compressCell_aux2 d A x) (compressCell_aux2 d A y) := by
  obtain ⟨k', hagree, hstep⟩ := h
  have hdiff : x k' ≠ y k' := by
    rcases hstep with h | h <;> omega
  have hk'A : k' ∈ A := by
    by_contra hnotin
    rw [hxz k' hnotin, hyz k' hnotin] at hdiff
    exact hdiff rfl
  let e := Finset.orderIsoOfFin A rfl
  obtain ⟨i', hi'⟩ := e.surjective ⟨k', hk'A⟩
  refine ⟨i', ?_, ?_⟩
  · intro j hj
    change x ((e j : ↥A).val) = y ((e j : ↥A).val)
    apply hagree
    intro heq
    apply hj
    have hval : ((e i' : ↥A).val) = k' := congrArg Subtype.val hi'
    have heq' : e j = e i' := by
      apply Subtype.ext
      show ((e j : ↥A).val) = ((e i' : ↥A).val)
      rw [heq, hval]
    exact e.injective heq'
  · change (y ((e i' : ↥A).val) = x ((e i' : ↥A).val) + 1 ∨
      x ((e i' : ↥A).val) = y ((e i' : ↥A).val) + 1)
    have hval : ((e i' : ↥A).val) = k' := congrArg Subtype.val hi'
    rw [hval]
    exact hstep

lemma expand_preserves_adj_aux2 (d : ℕ) (A : Finset (Fin d))
    (y1 y2 : latticeCell A.card)
    (h : faceAdjacent A.card y1 y2) :
    faceAdjacent d (expandCell_aux2 d A y1) (expandCell_aux2 d A y2) := by
  obtain ⟨i', hagree, hstep⟩ := h
  let e := Finset.orderIsoOfFin A rfl
  have hk' : ((e i' : ↥A).val) ∈ A := (e i').property
  refine ⟨(e i' : ↥A).val, ?_, ?_⟩
  · intro j hj
    show expandCell_aux2 d A y1 j = expandCell_aux2 d A y2 j
    simp only [expandCell_aux2]
    by_cases hjA : j ∈ A
    · rw [dite_eq_left hjA, dite_eq_left hjA]
      have hne : e.symm ⟨j, hjA⟩ ≠ i' := by
        intro heq
        apply hj
        have h1 : e (e.symm ⟨j, hjA⟩) = (⟨j, hjA⟩ : ↥A) :=
          OrderIso.apply_symm_apply e _
        rw [heq] at h1
        have h2 : ((e i' : ↥A).val) = j := congrArg Subtype.val h1
        exact h2.symm
      exact hagree _ hne
    · rw [dite_eq_right hjA, dite_eq_right hjA]
  · have hY1 : expandCell_aux2 d A y1 ((e i' : ↥A).val) = y1 i' := by
      simp only [expandCell_aux2]
      rw [dite_eq_left hk']
      have heq : (⟨((e i' : ↥A).val), hk'⟩ : ↥A) = e i' := Subtype.ext rfl
      rw [heq, OrderIso.symm_apply_apply]
    have hY2 : expandCell_aux2 d A y2 ((e i' : ↥A).val) = y2 i' := by
      simp only [expandCell_aux2]
      rw [dite_eq_left hk']
      have heq : (⟨((e i' : ↥A).val), hk'⟩ : ↥A) = e i' := Subtype.ext rfl
      rw [heq, OrderIso.symm_apply_apply]
    rw [hY2, hY1]
    exact hstep

lemma zero_outside_of_not_mem_support_aux (d : ℕ) (S : Finset (latticeCell d))
    (hC : isCanonicalCells d S) (k : Fin d) (hk : k ∉ supportFinset_aux d S)
    (x : latticeCell d) (hx : x ∈ S) : x k = 0 := by
  simp only [supportFinset_aux, Finset.mem_filter, Finset.mem_univ, true_and,
    not_exists] at hk
  have hall : ∀ y ∈ S, x k = y k := by
    intro y hy
    by_contra hne
    exact hk x ⟨hx, y, hy, hne⟩
  obtain ⟨x0, hx0, hx0k⟩ := (hC k).1
  have h := hall x0 hx0
  rw [hx0k] at h
  exact h

lemma properDimension_lt_aux (d n : ℕ) (P : fixedPolycube d n) :
    properDimension d P.val < n := by
  rw [properDimension_eq_support_aux]
  exact support_card_lt_aux d n P.val P.2.1 P.2.2.1

lemma vanish_DX_ge_aux (n i : ℕ) (h : n ≤ i) : properFixedPolycubeCount n i = 0 := by
  unfold properFixedPolycubeCount
  rw [Nat.card_eq_zero]
  left
  constructor
  intro Q
  obtain ⟨P, hP⟩ := Q
  -- P : fixedPolycube i n with properDimension = i, but < n ≤ i contradiction
  have hlt := properDimension_lt_aux i n P
  omega

end MetaMathlibExt
end
