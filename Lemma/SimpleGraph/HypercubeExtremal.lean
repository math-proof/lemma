import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.SimpleGraph.HypercubeExtremal
open SimpleGraph


namespace SimpleGraph

/--
[hypercubeGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean)
-/
@[path]
lemma hypercubeGraph_adj
  {n : ℕ}
  {x y : Fin n → Bool} :
-- imply
  (hypercubeGraph n).Adj x y ↔ ∃! i, x i ≠ y i := by
-- proof
  unfold hypercubeGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · obtain ⟨i, hi, huniq⟩ := h
      exact ⟨i, Ne.symm hi, fun j hj => huniq j (Ne.symm hj)⟩
  · intro h
    have hne : x ≠ y := by
      obtain ⟨i, hi, _⟩ := h
      exact fun heq => hi (congrFun heq i)
    exact ⟨hne, Or.inl h⟩

end SimpleGraph

namespace SimpleGraph

/--
[hypercubeGraph_zero_not_adj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean)
-/
@[path]
lemma hypercubeGraph_zero_not_adj
  {x y : Fin 0 → Bool} :
-- imply
  ¬ (hypercubeGraph 0).Adj x y := by
-- proof
  rw [hypercubeGraph_adj]
  rintro ⟨i, _, _⟩
  exact Fin.elim0 i

end SimpleGraph

namespace SimpleGraph

/--
[hypercubeGraph_one_adj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean)
-/
@[path]
lemma hypercubeGraph_one_adj
  :
-- imply
  (hypercubeGraph 1).Adj (fun _ => true) (fun _ => false) := by
-- proof
  rw [hypercubeGraph_adj]
  exact ⟨0, by simp, fun j _ => Subsingleton.elim j 0⟩

end SimpleGraph

namespace SimpleGraph

/--
[hypercubeGraph_zero_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean)
-/
@[path]
lemma hypercubeGraph_zero_edgeSet
  :
-- imply
  (hypercubeGraph 0).edgeSet = ∅ := by
-- proof
  rw [SimpleGraph.edgeSet_eq_empty]
  ext x y
  constructor
  · exact hypercubeGraph_zero_not_adj x y
  · intro h
    simp at h

end SimpleGraph

namespace SimpleGraph

/--
[hypercubeGraph_subgraph_edgeSet_ncard_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean)
-/
@[path]
lemma hypercubeGraph_subgraph_edgeSet_ncard_le
  {n : ℕ}
  {S : Subgraph (hypercubeGraph n)} :
-- imply
  S.edgeSet.ncard ≤ (hypercubeGraph n).edgeSet.ncard :=
-- proof
  Set.ncard_le_ncard S.edgeSet_subset (Set.toFinite _)

end SimpleGraph

namespace SimpleGraph

/--
[le_hypercubeTuranNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean)
-/
@[path]
lemma le_hypercubeTuranNumber
  {n : ℕ}
  {H : SimpleGraph W}
  {S : Subgraph (hypercubeGraph n)}
-- given
  (hfree : H.Free S.coe) :
-- imply
  S.edgeSet.ncard ≤ hypercubeTuranNumber n H := by
-- proof
  classical
  unfold hypercubeTuranNumber
  have hmem : S.edgeSet.ncard ∈
    ((Finset.range ((hypercubeGraph n).edgeSet.ncard + 1)).filter
      (fun m => ∃ S : Subgraph (hypercubeGraph n), H.Free S.coe ∧ S.edgeSet.ncard = m)) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hypercubeGraph_subgraph_edgeSet_ncard_le n S), S, hfree, rfl⟩
  have h := Finset.le_sup hmem (f := id)
  simpa using h

end SimpleGraph

namespace SimpleGraph

/--
[hypercubeTuranNumber_le_edgeSet_ncard](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean)
-/
@[path]
lemma hypercubeTuranNumber_le_edgeSet_ncard
  {n : ℕ}
  {H : SimpleGraph W} :
-- imply
  hypercubeTuranNumber n H ≤ (hypercubeGraph n).edgeSet.ncard := by
-- proof
  classical
  unfold hypercubeTuranNumber
  apply Finset.sup_le
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  obtain ⟨_, S, _, rfl⟩ := hm
  simpa using hypercubeGraph_subgraph_edgeSet_ncard_le n S

end SimpleGraph

namespace SimpleGraph

/--
[exists_attains_hypercubeTuranNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean)
-/
@[path]
lemma exists_attains_hypercubeTuranNumber
  {n : ℕ}
  {H : SimpleGraph W}
-- given
  (hne : ∃ S : Subgraph (hypercubeGraph n), H.Free S.coe) :
-- imply
  ∃ S : Subgraph (hypercubeGraph n),
    H.Free S.coe ∧ S.edgeSet.ncard = hypercubeTuranNumber n H := by
-- proof
  classical
  obtain ⟨S₀, hfree₀⟩ := hne
  have hmem₀ : S₀.edgeSet.ncard ∈
    ((Finset.range ((hypercubeGraph n).edgeSet.ncard + 1)).filter
      (fun m => ∃ S : Subgraph (hypercubeGraph n),
        H.Free S.coe ∧ S.edgeSet.ncard = m)) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hypercubeGraph_subgraph_edgeSet_ncard_le n S₀), S₀, hfree₀, rfl⟩
  have hne' : (((Finset.range ((hypercubeGraph n).edgeSet.ncard + 1)).filter
    (fun m => ∃ S : Subgraph (hypercubeGraph n),
      H.Free S.coe ∧ S.edgeSet.ncard = m)) : Finset ℕ).Nonempty :=
    ⟨_, hmem₀⟩
  obtain ⟨m, hm, hsup⟩ := Finset.exists_mem_eq_sup _ hne' (id : ℕ → ℕ)
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  obtain ⟨_, S, hfree, rfl⟩ := hm
  exact ⟨S, hfree, hsup.symm⟩

end SimpleGraph

namespace SimpleGraph

/--
[hypercubeTuranNumber_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean)
-/
@[path]
lemma hypercubeTuranNumber_zero
  {H : SimpleGraph W} :
-- imply
  hypercubeTuranNumber 0 H = 0 := by
-- proof
  have h := hypercubeTuranNumber_le_edgeSet_ncard 0 H
  rw [hypercubeGraph_zero_edgeSet, Set.ncard_empty] at h
  exact Nat.le_zero.mp h

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-26
