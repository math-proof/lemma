import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.BipartiteSubgraph
open Finset BigOperators SimpleGraph BipartiteSubgraph


namespace BipartiteSubgraph

/--
[flipAt_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/BipartiteSubgraph.lean)
-/
@[path]
lemma flipAt_involutive
  [Fintype V]
  [DecidableEq V]
  [DecidableEq V]
  {v : V} :
-- imply
  Function.Involutive (flipAt v : (V → Bool) → (V → Bool)) := by
-- proof
  intro f; ext w; simp only [flipAt, Function.update]; split_ifs with h <;> simp_all

end BipartiteSubgraph

namespace BipartiteSubgraph

/--
[flipAt_bne_eq_not](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/BipartiteSubgraph.lean)
-/
@[path]
lemma flipAt_bne_eq_not
  [Fintype V]
  [DecidableEq V]
  [DecidableEq V]
  {u v : V}
  {f : V → Bool}
-- given
  (huv : u ≠ v) :
-- imply
  (flipAt v f u != flipAt v f v) = !(f u != f v) := by
-- proof
  simp only [flipAt, Function.update_of_ne huv, Function.update_self]
  obtain h | h <;> := Bool.eq_false_or_eq_true (f u)
    obtain h' | h' <;> simp [h, h'] := Bool.eq_false_or_eq_true (f v)

end BipartiteSubgraph

namespace BipartiteSubgraph

/--
[two_mul_card_filter_bne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/BipartiteSubgraph.lean)
-/
@[path]
lemma two_mul_card_filter_bne
  [Fintype V]
  [DecidableEq V]
  {u v : V}
-- given
  (huv : u ≠ v) :
-- imply
  2 * ((univ : Finset (V → Bool)).filter (fun f => f u != f v)).card = Fintype.card (V → Bool) := by
-- proof
  classical
  set S := univ.filter (fun f : V → Bool => f u != f v)
  set T := univ.filter (fun f : V → Bool => !(f u != f v))
  have hST : S.card + T.card = Fintype.card (V → Bool) := by
    rw [← card_univ (α := V → Bool), ← card_union_of_disjoint]
    · congr 1; ext f; simp [S, T]; tauto
    · exact disjoint_filter.mpr (fun f _ h => by simp [h])
  suffices h : S.card = T.card by omega
  apply card_nbij (flipAt v)
  · intro f hf
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and, S] at hf
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and, T]
    rw [flipAt_bne_eq_not huv, hf]; rfl
  · intro f₁ _ f₂ _ heq; exact (flipAt_involutive v).injective heq
  · intro f hf
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and, T] at hf
    refine ⟨flipAt v f, ?_, flipAt_involutive v f⟩
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and, S]
    rw [flipAt_bne_eq_not huv]; simp only [Bool.not_eq_true'] at hf; rw [hf]; rfl

end BipartiteSubgraph

namespace BipartiteSubgraph

/--
[double_count_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/BipartiteSubgraph.lean)
-/
@[path]
lemma double_count_sum
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  2 * ∑ f : V → Bool, (G.edgeFinset.filter (fun e => boolCut f e)).card = G.edgeFinset.card * Fintype.card (V → Bool) := by
-- proof
  simp_rw [card_filter]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (s := univ) (t := G.edgeFinset)]
  simp_rw [← Finset.mul_sum, ← card_filter]
  rw [Finset.mul_sum]
  rw [show G.edgeFinset.card * Fintype.card (V → Bool) =
    G.edgeFinset.card • Fintype.card (V → Bool) from (smul_eq_mul _ _).symm]
  apply Finset.sum_eq_card_nsmul
  intro e he
  rw [SimpleGraph.mem_edgeFinset] at he
  induction e using Sym2.ind with
  | h u v =>
    simp only [boolCut_mk]
    exact two_mul_card_filter_bne u v he.ne

end BipartiteSubgraph

namespace BipartiteSubgraph

/--
[exists_bipartite_subgraph_half_edges](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/BipartiteSubgraph.lean)
-/
@[path]
lemma exists_bipartite_subgraph_half_edges
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∃ f : V → Bool, G.edgeFinset.card / 2 ≤ (G.edgeFinset.filter (fun e => boolCut f e)).card := by
-- proof
  by_contra h
  push Not at h
  have hN : (univ : Finset (V → Bool)).Nonempty := ⟨fun _ => true, mem_univ _⟩
  have hsum_lt := sum_lt_sum_of_nonempty hN (fun f _ => h f)
  simp only [sum_const, smul_eq_mul, card_univ] at hsum_lt
  nlinarith [double_count_sum G, Nat.mul_div_le G.edgeFinset.card 2]

end BipartiteSubgraph

namespace BipartiteSubgraph

/--
[cutGraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/BipartiteSubgraph.lean)
-/
@[path]
lemma cutGraph_le
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {f : V → Bool} :
-- imply
  cutGraph G f ≤ G :=
-- proof
  fun _ _ h => h.1

end BipartiteSubgraph

namespace BipartiteSubgraph

/--
[cutGraph_isBipartite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/BipartiteSubgraph.lean)
-/
@[path]
lemma cutGraph_isBipartite
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {f : V → Bool} :
-- imply
  (cutGraph G f).Colorable 2 := by
-- proof
  refine ⟨⟨fun v => if f v then 0 else 1, fun {u v} h => ?_⟩⟩
  obtain ⟨_, hne⟩ := h
  obtain hu | hu <;> := Bool.eq_false_or_eq_true (f u)
    obtain hv | hv <;> := Bool.eq_false_or_eq_true (f v)
    simp_all

end BipartiteSubgraph

namespace BipartiteSubgraph

/--
[cutGraph_edgeFinset_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/BipartiteSubgraph.lean)
-/
@[path]
lemma cutGraph_edgeFinset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f : V → Bool}
  [Fintype (cutGraph G f).edgeSet] :
-- imply
  (cutGraph G f).edgeFinset = G.edgeFinset.filter (fun e => boolCut f e) := by
-- proof
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_filter]
  constructor
  · intro he
    induction e using Sym2.ind with
    | h u v => exact ⟨he.1, by simp [boolCut_mk, bne_iff_ne, he.2]⟩
  · intro ⟨he, hcut⟩
    induction e using Sym2.ind with
    | h u v =>
      simp [boolCut_mk, bne_iff_ne] at hcut
      exact ⟨he, hcut⟩

end BipartiteSubgraph

namespace BipartiteSubgraph

/--
[exists_bipartite_subgraph](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/BipartiteSubgraph.lean)
-/
@[path]
lemma exists_bipartite_subgraph
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∃ H : SimpleGraph V, H ≤ G ∧ H.Colorable 2 ∧ ∀ [Fintype H.edgeSet], G.edgeFinset.card / 2 ≤ H.edgeFinset.card := by
-- proof
  obtain ⟨f, hf⟩ := exists_bipartite_subgraph_half_edges G
  refine ⟨cutGraph G f, cutGraph_le G f, cutGraph_isBipartite G f, fun {_} => ?_⟩
  rwa [cutGraph_edgeFinset_eq]

end BipartiteSubgraph

/--
[bne_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/BipartiteSubgraph.lean)
-/
@[path]
private lemma bne_symm_eq
  [Fintype V]
  [DecidableEq V]
  {f : V → Bool}
  {a b : V} :
-- imply
  (f a != f b) = (f b != f a) := by
-- proof
  apply BipartiteSubgraph.bne_symm f a b

/--
[boolCut_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/BipartiteSubgraph.lean)
-/
@[path]
private lemma boolCut_mk_eq
  [Fintype V]
  [DecidableEq V]
  {f : V → Bool}
  {u v : V} :
-- imply
  boolCut f s(u, v) = (f u != f v) := by
-- proof
  apply BipartiteSubgraph.boolCut_mk f u v


-- created on 2026-10-23
