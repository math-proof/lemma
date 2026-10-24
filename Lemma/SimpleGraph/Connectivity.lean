import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Connectivity
open SimpleGraph
open Finset List


namespace SimpleGraph

/--
[mem_bfsStep](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Connectivity.lean)
-/
@[path]
lemma mem_bfsStep
  {G : SimpleGraph V}
  [Fintype V]
  [DecidableEq V]
  [DecidableRel G.Adj]
  {m n : ℕ}
  {s t : Finset V}
  {u v w : V}
  (G s) :
-- imply
  w ∈ G.bfsStep s ↔ w ∈ s ∨ ∃ v ∈ s, G.Adj v w := by
-- proof
simp [bfsStep]

end SimpleGraph

namespace SimpleGraph

/--
[subset_bfsStep](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Connectivity.lean)
-/
@[path]
lemma subset_bfsStep
  {G : SimpleGraph V}
  [Fintype V]
  [DecidableEq V]
  [DecidableRel G.Adj]
  {m n : ℕ}
  {s t : Finset V}
  {u v w : V}
  (G s) :
-- imply
  s ⊆ G.bfsStep s :=
-- proof
  fun _ hw ↦ G.mem_bfsStep.2 <| .inl hw

end SimpleGraph

namespace SimpleGraph

/--
[iterate_bfsStep_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Connectivity.lean)
-/
@[path]
lemma iterate_bfsStep_mono
  {G : SimpleGraph V}
  [Fintype V]
  [DecidableEq V]
  [DecidableRel G.Adj]
  {m n : ℕ}
  {s t : Finset V}
  {u v w : V}
  (G s)
-- given
  (hst : s ⊆ t) :
-- imply
  G.bfsStep^[n] s ⊆ G.bfsStep^[n] t := by
-- proof
  induction n generalizing s t with
  | zero => exact hst
  | succ n ih => simpa only [Function.iterate_succ_apply] using ih (G.bfsStep_mono hst)

end SimpleGraph

namespace SimpleGraph

/--
[subset_iterate_bfsStep](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Connectivity.lean)
-/
@[path]
lemma subset_iterate_bfsStep
  {G : SimpleGraph V}
  [Fintype V]
  [DecidableEq V]
  [DecidableRel G.Adj]
  {m n : ℕ}
  {s t : Finset V}
  {u v w : V}
  (G s) :
-- imply
  s ⊆ G.bfsStep^[n] s := by
-- proof
  induction n with
  | zero => exact subset_rfl
  | succ n ih => grw [Function.iterate_succ_apply', ← ih, ← G.subset_bfsStep]

end SimpleGraph

namespace SimpleGraph

/--
[iterate_bfsStep_subset_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Connectivity.lean)
-/
@[path]
lemma iterate_bfsStep_subset_of_le
  {G : SimpleGraph V}
  [Fintype V]
  [DecidableEq V]
  [DecidableRel G.Adj]
  {m n : ℕ}
  {s t : Finset V}
  {u v w : V}
  (G s)
-- given
  (hmn : m ≤ n) :
-- imply
  G.bfsStep^[m] s ⊆ G.bfsStep^[n] s := by
-- proof
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Function.iterate_add_apply]
  exact G.iterate_bfsStep_mono G.subset_iterate_bfsStep

end SimpleGraph

namespace SimpleGraph

/--
[mem_iterate_bfsStep_of_walk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Connectivity.lean)
-/
@[path]
lemma mem_iterate_bfsStep_of_walk
  {G : SimpleGraph V}
  [Fintype V]
  [DecidableEq V]
  [DecidableRel G.Adj]
  {m n : ℕ}
  {s t : Finset V}
  {u v w : V}
  (G s)
  {p : G.Walk u v} :
-- imply
  v ∈ G.bfsStep^[p.length] {u} := by
-- proof
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [Walk.length_cons, Function.iterate_succ_apply]
    exact G.iterate_bfsStep_mono (by simp [h]) ih

end SimpleGraph

namespace SimpleGraph

/--
[reachable_of_mem_iterate_bfsStep](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Connectivity.lean)
-/
@[path]
lemma reachable_of_mem_iterate_bfsStep
  {G : SimpleGraph V}
  [Fintype V]
  [DecidableEq V]
  [DecidableRel G.Adj]
  {m n : ℕ}
  {s t : Finset V}
  {u v w : V}
  (G s)
-- given
  (hv : v ∈ G.bfsStep^[n] {u}) :
-- imply
  G.Reachable u v := by
-- proof
  induction n generalizing v with
  | zero =>
    rw [Function.iterate_zero_apply, Finset.mem_singleton] at hv
    exact hv ▸ Reachable.refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply', mem_bfsStep] at hv
    obtain hv | ⟨w, hw, hwv⟩ := hv
    · exact ih hv
    · exact (ih hw).trans hwv.reachable

end SimpleGraph

namespace SimpleGraph

/--
[bfsIterate_eq_iterate_bfsStep](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Connectivity.lean)
-/
@[path]
lemma bfsIterate_eq_iterate_bfsStep
  {G : SimpleGraph V}
  [Fintype V]
  [DecidableEq V]
  [DecidableRel G.Adj]
  {m n : ℕ}
  {s t : Finset V}
  {u v w : V}
  (G s)
  {n : ℕ}
  {s : Finset V} :
-- imply
  G.bfsIterate n s = G.bfsStep^[n] s := by
-- proof
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [bfsIterate]
    split_ifs with h
    · have hs : G.bfsStep s = s := (Finset.eq_of_subset_of_card_le G.subset_bfsStep h).symm
      exact (Function.iterate_fixed hs _).symm
    · rw [ih, ← Function.iterate_succ_apply]

end SimpleGraph

namespace SimpleGraph

/--
[mem_reachableFinset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Connectivity.lean)
-/
@[path]
lemma mem_reachableFinset
  {G : SimpleGraph V}
  [Fintype V]
  [DecidableEq V]
  [DecidableRel G.Adj]
  {m n : ℕ}
  {s t : Finset V}
  {u v w : V}
  (G s) :
-- imply
  v ∈ G.reachableFinset u ↔ G.Reachable u v := by
-- proof
  rw [reachableFinset, bfsIterate_eq_iterate_bfsStep]
  refine ⟨G.reachable_of_mem_iterate_bfsStep, fun h ↦ h.elim_path fun p ↦ ?_⟩
  exact G.iterate_bfsStep_subset_of_le p.2.length_lt.le (G.mem_iterate_bfsStep_of_walk p.1)

end SimpleGraph

namespace SimpleGraph

/--
[preconnected_iff_forall_mem_reachableFinset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Connectivity.lean)
-/
@[path]
lemma preconnected_iff_forall_mem_reachableFinset
  {G : SimpleGraph V}
  [Fintype V]
  [DecidableEq V]
  [DecidableRel G.Adj]
  {m n : ℕ}
  {s t : Finset V}
  {u v w : V}
  (G s)
  {u : V} :
-- imply
  G.Preconnected ↔ ∀ v, v ∈ G.reachableFinset u := by
-- proof
  simp only [mem_reachableFinset]
  exact ⟨fun h v ↦ h u v, fun h x y ↦ (h x).symm.trans (h y)⟩

end SimpleGraph

namespace SimpleGraph

/--
[connected_iff_forall_mem_reachableFinset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Connectivity.lean)
-/
@[path]
lemma connected_iff_forall_mem_reachableFinset
  {G : SimpleGraph V}
  [Fintype V]
  [DecidableEq V]
  [DecidableRel G.Adj]
  {m n : ℕ}
  {s t : Finset V}
  {u v w : V}
  (G s)
  {u : V} :
-- imply
  G.Connected ↔ ∀ v, v ∈ G.reachableFinset u := by
-- proof
  rw [connected_iff, G.preconnected_iff_forall_mem_reachableFinset u, and_iff_left ⟨u⟩]

end SimpleGraph

/--
[bfsStep_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Connectivity.lean)
-/
@[path]
private lemma bfsStep_mono_eq
  {G : SimpleGraph V}
  [Fintype V]
  [DecidableEq V]
  [DecidableRel G.Adj]
  {m n : ℕ}
  {s t : Finset V}
  {u v w : V}
  (G s)
-- given
  (hst : s ⊆ t) :
-- imply
  G.bfsStep s ⊆ G.bfsStep t := by
-- proof
  apply SimpleGraph.bfsStep_mono hst


-- created on 2026-10-23
