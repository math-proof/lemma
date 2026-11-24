module
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Choose.Sum
public import Theorem.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/
section

namespace MetaMathlibExt

open scoped BigOperators

noncomputable def fiberToProper_aux (d n : ℕ) (A : Finset (Fin d))
    (P : fiberSet_aux d n A) : properFixedPolycube n A.card :=
  match P with
  | ⟨⟨S, hP, hnS, hC⟩, hsup⟩ =>
    have hz : ∀ x ∈ S, ∀ k : Fin d, k ∉ A → x k = 0 := by
      intro x hx k hkA
      have hkn : k ∉ supportFinset_aux d S := by
        rw [hsup]
        exact hkA
      exact zero_outside_of_not_mem_support_aux d S hC k hkn x hx
    ⟨⟨compressSet_aux2 d A S,
      conn_compressSet_aux d A S hP hz,
      by rw [card_compressSet_aux d A S hz, hnS],
      canon_compressSet_aux d A S hC⟩,
    by rw [properDimension_eq_support_aux, support_compressSet_aux d A S hsup,
      Finset.card_univ, Fintype.card_fin]⟩

noncomputable def properToFiber_aux (d n : ℕ) (A : Finset (Fin d))
    (Q : properFixedPolycube n A.card) : fiberSet_aux d n A :=
  match Q with
  | ⟨⟨T, hPT, hnT, hCT⟩, hproper⟩ =>
    have hsupT : supportFinset_aux A.card T = Finset.univ := by
      have h1 : (supportFinset_aux A.card T).card = Fintype.card (Fin A.card) := by
        rw [← properDimension_eq_support_aux, hproper, Fintype.card_fin]
      exact Finset.eq_univ_of_card _ h1
    ⟨⟨expandSet_aux2 d A T,
      conn_expandSet_aux d A T hPT,
      by rw [card_expandSet_aux d A T, hnT],
      canon_expandSet_aux d A T hPT.1 hCT⟩,
    support_expandSet_aux d A T hsupT⟩

end MetaMathlibExt
end
