import Mathlib
import Initialize.Tactic.Attr.Basic
open Finset BigOperators


namespace SimpleGraph

/--
[exists_indepSet_of_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/IndependentSets.lean)
-/
@[path]
lemma exists_indepSet_of_sum_le
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V} :
-- imply
  ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet (↑I : Set V) ∧ ∑ v ∈ S, (1 : ℚ) / ((G.degree v : ℚ) + 1) ≤ ↑I.card := by
-- proof
  induction S using Finset.strongInduction with
  | _ S ih =>
    by_cases hS : S = ∅
    · subst hS
      exact ⟨∅, empty_subset _, by simp [IsIndepSet, Set.Pairwise], by simp⟩
    · have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
      obtain ⟨v, hv, hmin⟩ := Finset.exists_min_image S (fun w => G.degree w) hne
      set T := {v} ∪ G.neighborFinset v with hT_def
      set S' := S \ T with hS'_def
      have hS'_ssubset : S' ⊂ S := by
        constructor
        · exact sdiff_subset
        · intro h; have : v ∈ S' := h hv; simp [hS'_def, hT_def] at this
      obtain ⟨I', hI'sub, hI'indep, hI'bound⟩ := ih S' hS'_ssubset
      have hv_notin_I' : v ∉ I' := by
        intro hv'; have := hI'sub hv'; simp [hS'_def, hT_def] at this
      refine ⟨insert v I', ?_, ?_, ?_⟩
      ·
        intro w hw
        simp only [mem_insert] at hw
        obtain rfl | hw := hw
        · exact hv
        · exact sdiff_subset (hI'sub hw)
      ·
        rw [isIndepSet_iff]
        intro a ha b hb hab
        simp only [coe_insert, Set.mem_insert_iff, mem_coe] at ha hb
        obtain rfl | ha <;> rcases hb with rfl | hb := ha
        · exact absurd rfl hab
        · intro hadj
          have hb' := hI'sub hb
          simp only [hS'_def, hT_def, mem_sdiff, mem_union, mem_singleton,
            mem_neighborFinset] at hb'
          exact hb'.2 (Or.inr hadj)
        · intro hadj
          have ha' := hI'sub ha
          simp only [hS'_def, hT_def, mem_sdiff, mem_union, mem_singleton,
            mem_neighborFinset] at ha'
          exact ha'.2 (Or.inr (G.symm hadj))
        · exact hI'indep (mem_coe.mpr ha) (mem_coe.mpr hb) hab
      ·
        rw [Finset.card_insert_of_notMem hv_notin_I']
        have hsum : ∑ w ∈ S, (1 : ℚ) / ((G.degree w : ℚ) + 1) =
          ∑ w ∈ S', (1 : ℚ) / ((G.degree w : ℚ) + 1) +
          ∑ w ∈ S ∩ T, (1 : ℚ) / ((G.degree w : ℚ) + 1) := by
          rw [← Finset.sum_union (disjoint_sdiff_inter S T)]
          congr 1; exact (sdiff_union_inter S T).symm
        rw [hsum]
        have hremoved : ∑ w ∈ S ∩ T, (1 : ℚ) / ((G.degree w : ℚ) + 1) ≤ 1 := by
          have hcard : (S ∩ T).card ≤ G.degree v + 1 := by
            calc (S ∩ T).card ≤ T.card := card_le_card inter_subset_right
              _ = G.degree v + 1 := by
                simp only [hT_def,
                  card_union_of_disjoint (G.singleton_disjoint_neighborFinset v),
                  card_singleton, G.card_neighborFinset_eq_degree]
                ring
          have hbnd : ∀ w ∈ S ∩ T,
            (1 : ℚ) / ((G.degree w : ℚ) + 1) ≤ 1 / ((G.degree v : ℚ) + 1) := by
            intro w hw
            have hwS : w ∈ S := (mem_inter.mp hw).1
            have hdeg : G.degree v ≤ G.degree w := hmin w hwS
            exact Nat.one_div_le_one_div hdeg
          have hdv_ne : (G.degree v : ℚ) + 1 ≠ 0 := by positivity
          calc ∑ w ∈ S ∩ T, (1 : ℚ) / ((G.degree w : ℚ) + 1)
            ≤ (S ∩ T).card • (1 / ((G.degree v : ℚ) + 1)) :=
              sum_le_card_nsmul _ _ _ hbnd
            _ ≤ (G.degree v + 1) • (1 / ((G.degree v : ℚ) + 1)) := by
              rw [nsmul_eq_mul, nsmul_eq_mul]
              have h_le : ((S ∩ T).card : ℚ) ≤ ((G.degree v + 1 : ℕ) : ℚ) := by
                exact_mod_cast hcard
              exact mul_le_mul_of_nonneg_right h_le (by positivity)
            _ = 1 := by
              rw [nsmul_eq_mul]
              rw [show ((G.degree v + 1 : ℕ) : ℚ) = (G.degree v : ℚ) + 1
                from by exact_mod_cast rfl]
              exact mul_div_cancel₀ 1 hdv_ne
        have hcast : (↑(I'.card + 1) : ℚ) = (↑I'.card : ℚ) + 1 := by exact_mod_cast rfl
        linarith [hcast]

end SimpleGraph

namespace SimpleGraph

/--
[caro_wei](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/IndependentSets.lean)
-/
@[path]
lemma caro_wei
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∃ I : Finset V, G.IsIndepSet (↑I : Set V) ∧ ∑ v : V, (1 : ℚ) / ((G.degree v : ℚ) + 1) ≤ ↑I.card := by
-- proof
  obtain ⟨I, _, hind, hcard⟩ := G.exists_indepSet_of_sum_le Finset.univ
  exact ⟨I, hind, hcard⟩

end SimpleGraph

namespace SimpleGraph

/--
[sum_compl_deg_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/IndependentSets.lean)
-/
@[path]
lemma sum_compl_deg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∑ v : V, (1 : ℚ) / ((Gᶜ.degree v : ℚ) + 1) = ∑ v : V, (1 : ℚ) / ((Fintype.card V : ℚ) - (G.degree v : ℚ)) := by
-- proof
  congr 1
  ext v
  congr 1
  have h := G.degree_compl v
  have hlt := G.degree_lt_card_verts v
  have hle : G.degree v ≤ Fintype.card V - 1 := Nat.le_sub_one_of_lt hlt
  rw [h]
  have h3 : (↑(Fintype.card V - 1 - G.degree v) : ℚ) = (Fintype.card V : ℚ) - 1 - (G.degree v : ℚ) := by
    rw [Nat.cast_sub hle, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (by omega))]
    simp [Nat.cast_one]
  linarith

end SimpleGraph

namespace SimpleGraph

/--
[caro_wei_clique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/IndependentSets.lean)
-/
@[path]
lemma caro_wei_clique
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∃ C : Finset V, G.IsClique (↑C : Set V) ∧ ∑ v : V, (1 : ℚ) / ((Fintype.card V : ℚ) - (G.degree v : ℚ)) ≤ ↑C.card := by
-- proof
  obtain ⟨I, hI_indep, hI_bound⟩ := Gᶜ.caro_wei
  refine ⟨I, ?_, ?_⟩
  · exact G.isIndepSet_compl.mp hI_indep
  · rw [← G.sum_compl_deg_eq]
    exact hI_bound

end SimpleGraph


-- created on 2026-10-23
