/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum
import Def.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part8


section

namespace MetaMathlibExt

open scoped BigOperators

-- compress is injective on cells vanishing outside A
lemma compress_injOn_zero_outside_aux (d : ℕ) (A : Finset (Fin d)) :
    Set.InjOn (compressCell_aux2 d A) { x | ∀ k : Fin d, k ∉ A → x k = 0 } := by
  intro x hx y hy hxy
  simp only [Set.mem_ofPred_eq] at hx hy
  have hx' : expandCell_aux2 d A (compressCell_aux2 d A x) = x :=
    expand_compress_aux2 d A x hx
  have hy' : expandCell_aux2 d A (compressCell_aux2 d A y) = y :=
    expand_compress_aux2 d A y hy
  rw [← hx', ← hy', hxy]

-- expand is always injective
lemma expand_injective_aux (d : ℕ) (A : Finset (Fin d)) :
    Function.Injective (expandCell_aux2 d A) := by
  intro y1 y2 h
  have h2 := congrArg (compressCell_aux2 d A) h
  rwa [compress_expand_aux2, compress_expand_aux2] at h2

lemma card_compressSet_aux (d : ℕ) (A : Finset (Fin d)) (S : Finset (latticeCell d))
    (hz : ∀ x ∈ S, ∀ k : Fin d, k ∉ A → x k = 0) :
    (compressSet_aux2 d A S).card = S.card := by
  unfold compressSet_aux2
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  simp only [Finset.mem_coe] at hx hy
  exact compress_injOn_zero_outside_aux d A (hz x hx) (hz y hy) hxy

lemma card_expandSet_aux (d : ℕ) (A : Finset (Fin d)) (T : Finset (latticeCell A.card)) :
    (expandSet_aux2 d A T).card = T.card := by
  unfold expandSet_aux2
  exact Finset.card_image_of_injective T (expand_injective_aux d A)

lemma canon_compressSet_aux (d : ℕ) (A : Finset (Fin d)) (S : Finset (latticeCell d))
    (hC : isCanonicalCells d S) :
    isCanonicalCells A.card (compressSet_aux2 d A S) := by
  intro j
  obtain ⟨x0, hx0, hx0k⟩ :=
    (hC ((Finset.orderIsoOfFin A rfl j : ↥A).val)).1
  constructor
  · refine ⟨compressCell_aux2 d A x0, Finset.mem_image_of_mem _ hx0, ?_⟩
    change x0 ((Finset.orderIsoOfFin A rfl j : ↥A).val) = 0
    exact hx0k
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    change 0 ≤ y ((Finset.orderIsoOfFin A rfl j : ↥A).val)
    exact (hC ((Finset.orderIsoOfFin A rfl j : ↥A).val)).2 y hy

lemma canon_expandSet_aux (d : ℕ) (A : Finset (Fin d)) (T : Finset (latticeCell A.card))
    (hTne : T.Nonempty) (hC : isCanonicalCells A.card T) :
    isCanonicalCells d (expandSet_aux2 d A T) := by
  intro k
  by_cases hk : k ∈ A
  · obtain ⟨y0, hy0, hy0j⟩ :=
      (hC ((Finset.orderIsoOfFin A rfl).symm ⟨k, hk⟩)).1
    constructor
    · refine ⟨expandCell_aux2 d A y0, Finset.mem_image_of_mem _ hy0, ?_⟩
      simp only [expandCell_aux2, dite_eq_left hk]
      exact hy0j
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      simp only [expandCell_aux2, dite_eq_left hk]
      exact (hC ((Finset.orderIsoOfFin A rfl).symm ⟨k, hk⟩)).2 y hy
  · constructor
    · obtain ⟨y0, hy0⟩ := hTne
      refine ⟨expandCell_aux2 d A y0, Finset.mem_image_of_mem _ hy0, ?_⟩
      simp only [expandCell_aux2, dite_eq_right hk]
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      simp only [expandCell_aux2, dite_eq_right hk, le_refl]

lemma conn_compressSet_aux (d : ℕ) (A : Finset (Fin d)) (S : Finset (latticeCell d))
    (hP : isPolycubeCells d S)
    (hz : ∀ x ∈ S, ∀ k : Fin d, k ∉ A → x k = 0) :
    isPolycubeCells A.card (compressSet_aux2 d A S) := by
  constructor
  · obtain ⟨x0, hx0⟩ := hP.1
    exact ⟨compressCell_aux2 d A x0, Finset.mem_image_of_mem _ hx0⟩
  · intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    have hRT := hP.2 x hx y hy
    have hmono : (fun a b : latticeCell d => faceAdjacent d a b ∧ a ∈ S ∧ b ∈ S) ≤
        Function.onFun (fun a' b' : latticeCell A.card =>
          faceAdjacent A.card a' b' ∧
            a' ∈ compressSet_aux2 d A S ∧ b' ∈ compressSet_aux2 d A S)
        (compressCell_aux2 d A) := by
      intro u v huv
      obtain ⟨hadj, huS, hvS⟩ := huv
      refine ⟨compress_preserves_adj_aux2 d A u v (hz u huS) (hz v hvS) hadj, ?_, ?_⟩
      · exact Finset.mem_image_of_mem _ huS
      · exact Finset.mem_image_of_mem _ hvS
    exact Relation.ReflTransGen.lift (compressCell_aux2 d A) hmono _ _ hRT

lemma conn_expandSet_aux (d : ℕ) (A : Finset (Fin d)) (T : Finset (latticeCell A.card))
    (hPT : isPolycubeCells A.card T) :
    isPolycubeCells d (expandSet_aux2 d A T) := by
  constructor
  · obtain ⟨y0, hy0⟩ := hPT.1
    exact ⟨expandCell_aux2 d A y0, Finset.mem_image_of_mem _ hy0⟩
  · intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    have hRT := hPT.2 u hu v hv
    have hmono : (fun a b : latticeCell A.card =>
          faceAdjacent A.card a b ∧ a ∈ T ∧ b ∈ T) ≤
        Function.onFun (fun a' b' : latticeCell d =>
          faceAdjacent d a' b' ∧
            a' ∈ expandSet_aux2 d A T ∧ b' ∈ expandSet_aux2 d A T)
        (expandCell_aux2 d A) := by
      intro u' v' huv
      obtain ⟨hadj, huT, hvT⟩ := huv
      refine ⟨expand_preserves_adj_aux2 d A u' v' hadj, ?_, ?_⟩
      · exact Finset.mem_image_of_mem _ huT
      · exact Finset.mem_image_of_mem _ hvT
    exact Relation.ReflTransGen.lift (expandCell_aux2 d A) hmono _ _ hRT

lemma support_compressSet_aux (d : ℕ) (A : Finset (Fin d)) (S : Finset (latticeCell d))
    (hsup : supportFinset_aux d S = A) :
    supportFinset_aux A.card (compressSet_aux2 d A S) = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro j
  simp only [supportFinset_aux, Finset.mem_filter, Finset.mem_univ, true_and]
  have hkA : (Finset.orderIsoOfFin A rfl j : ↥A).val ∈ A :=
    (Finset.orderIsoOfFin A rfl j).property
  have hkS : (Finset.orderIsoOfFin A rfl j : ↥A).val ∈ supportFinset_aux d S := by
    rw [hsup]
    exact hkA
  simp only [supportFinset_aux, Finset.mem_filter, Finset.mem_univ, true_and] at hkS
  obtain ⟨x, hx, y, hy, hxy⟩ := hkS
  refine ⟨compressCell_aux2 d A x, Finset.mem_image_of_mem _ hx,
    compressCell_aux2 d A y, Finset.mem_image_of_mem _ hy, ?_⟩
  change x ((Finset.orderIsoOfFin A rfl j : ↥A).val) ≠
    y ((Finset.orderIsoOfFin A rfl j : ↥A).val)
  exact hxy

lemma support_expandSet_aux (d : ℕ) (A : Finset (Fin d)) (T : Finset (latticeCell A.card))
    (hsup : supportFinset_aux A.card T = Finset.univ) :
    supportFinset_aux d (expandSet_aux2 d A T) = A := by
  ext k
  simp only [supportFinset_aux, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, hu, v, hv, hne⟩
    by_contra hkA
    obtain ⟨y1, hy1, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y2, hy2, rfl⟩ := Finset.mem_image.mp hv
    have e1 : expandCell_aux2 d A y1 k = 0 := by
      simp only [expandCell_aux2, dite_eq_right hkA]
    have e2 : expandCell_aux2 d A y2 k = 0 := by
      simp only [expandCell_aux2, dite_eq_right hkA]
    rw [e1, e2] at hne
    exact hne rfl
  · intro hkA
    have hjU : (Finset.orderIsoOfFin A rfl).symm ⟨k, hkA⟩ ∈
        (Finset.univ : Finset (Fin A.card)) := Finset.mem_univ _
    rw [← hsup] at hjU
    simp only [supportFinset_aux, Finset.mem_filter, Finset.mem_univ, true_and] at hjU
    obtain ⟨y1, hy1, y2, hy2, hne⟩ := hjU
    refine ⟨expandCell_aux2 d A y1, Finset.mem_image_of_mem _ hy1,
      expandCell_aux2 d A y2, Finset.mem_image_of_mem _ hy2, ?_⟩
    show expandCell_aux2 d A y1 k ≠ expandCell_aux2 d A y2 k
    simp only [expandCell_aux2, dite_eq_left hkA]
    exact hne

lemma expand_compressSet_aux2 (d : ℕ) (A : Finset (Fin d)) (S : Finset (latticeCell d))
    (hz : ∀ x ∈ S, ∀ k : Fin d, k ∉ A → x k = 0) :
    expandSet_aux2 d A (compressSet_aux2 d A S) = S := by
  unfold expandSet_aux2 compressSet_aux2
  rw [Finset.image_image]
  have h : Set.EqOn (expandCell_aux2 d A ∘ compressCell_aux2 d A) id ↑S := by
    intro x hx
    simp only [Finset.mem_coe] at hx
    change expandCell_aux2 d A (compressCell_aux2 d A x) = id x
    rw [expand_compress_aux2 d A x (hz x hx)]
    rfl
  rw [Finset.image_congr h, Finset.image_id]

lemma compress_expandSet_aux2 (d : ℕ) (A : Finset (Fin d))
    (T : Finset (latticeCell A.card)) :
    compressSet_aux2 d A (expandSet_aux2 d A T) = T := by
  unfold compressSet_aux2 expandSet_aux2
  rw [Finset.image_image]
  have h : Set.EqOn (compressCell_aux2 d A ∘ expandCell_aux2 d A) id ↑T := by
    intro y _
    change compressCell_aux2 d A (expandCell_aux2 d A y) = id y
    rw [compress_expand_aux2 d A y]
    rfl
  rw [Finset.image_congr h, Finset.image_id]

end MetaMathlibExt
end
