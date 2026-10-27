import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.CombinatorialOptimization.code.Flow.MaxFlowMinCut.Part2
open Finset BigOperators Classical NetworkFlow


namespace NetworkFlow

/--
[resCap'_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/MaxFlowMinCut.lean)
-/
@[path]
lemma resCap'_nonneg
  [Fintype V]
  [DecidableEq V]
  {N : FlowNetwork V}
  {fl : STFlow N}
  {u v : V} :
-- imply
  0 ≤ resCap' N fl u v := by
-- proof
  unfold resCap'
  linarith [fl.flow_nonneg v u, fl.flow_cap u v]

end NetworkFlow

namespace NetworkFlow

/--
[ResReachable_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/MaxFlowMinCut.lean)
-/
@[path]
lemma ResReachable_step
  [Fintype V]
  [DecidableEq V]
  {N : FlowNetwork V}
  {fl : STFlow N}
  {u v : V}
-- given
  (hu : ResReachable N fl u)
  (hadj : resAdj' N fl u v) :
-- imply
  ResReachable N fl v :=
-- proof
  hu.tail hadj

end NetworkFlow

namespace NetworkFlow

/--
[maxFlowCut_S](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/MaxFlowMinCut.lean)
-/
@[path]
lemma maxFlowCut_S
  [Fintype V]
  [DecidableEq V]
  {N : FlowNetwork V}
  {fl : STFlow N}
-- given
  (hmax : NoAugmentingPath N fl) :
-- imply
  (maxFlowCut N fl hmax).S = resReachableSet N fl :=
-- proof
  rfl

end NetworkFlow

namespace NetworkFlow

/--
[not_resAdj_of_reach_nonreach](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/MaxFlowMinCut.lean)
-/
@[path]
lemma not_resAdj_of_reach_nonreach
  [Fintype V]
  [DecidableEq V]
  {N : FlowNetwork V}
  {fl : STFlow N}
  {u v : V}
-- given
  (hu : ResReachable N fl u)
  (hv : ¬ ResReachable N fl v) :
-- imply
  ¬ resAdj' N fl u v := by
-- proof
  intro hadj
  exact hv (ResReachable_step hu hadj)

end NetworkFlow

namespace NetworkFlow

/--
[resCap'_eq_zero_of_cross](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/MaxFlowMinCut.lean)
-/
@[path]
lemma resCap'_eq_zero_of_cross
  [Fintype V]
  [DecidableEq V]
  {N : FlowNetwork V}
  {fl : STFlow N}
  {u v : V}
-- given
  (hu : ResReachable N fl u)
  (hv : ¬ ResReachable N fl v) :
-- imply
  resCap' N fl u v = 0 := by
-- proof
  have hnadj := not_resAdj_of_reach_nonreach hu hv
  unfold resAdj' at hnadj
  have hge := resCap'_nonneg N fl u v
  linarith

end NetworkFlow

namespace NetworkFlow

/--
[flow_eq_cap_of_cross](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/MaxFlowMinCut.lean)
-/
@[path]
lemma flow_eq_cap_of_cross
  [Fintype V]
  [DecidableEq V]
  {N : FlowNetwork V}
  {fl : STFlow N}
  {u v : V}
-- given
  (hu : ResReachable N fl u)
  (hv : ¬ ResReachable N fl v) :
-- imply
  fl.f u v = N.cap u v := by
-- proof
  have hrc := resCap'_eq_zero_of_cross hu hv
  unfold resCap' at hrc
  have hfv := fl.flow_nonneg v u
  have hfc := fl.flow_cap u v
  linarith

end NetworkFlow

namespace NetworkFlow

/--
[flow_eq_zero_of_cross](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/MaxFlowMinCut.lean)
-/
@[path]
lemma flow_eq_zero_of_cross
  [Fintype V]
  [DecidableEq V]
  {N : FlowNetwork V}
  {fl : STFlow N}
  {u v : V}
-- given
  (hu : ResReachable N fl u)
  (hv : ¬ ResReachable N fl v) :
-- imply
  fl.f v u = 0 := by
-- proof
  have hrc := resCap'_eq_zero_of_cross hu hv
  unfold resCap' at hrc
  have hfc := fl.flow_cap u v
  have hfn := fl.flow_nonneg v u
  linarith

end NetworkFlow

namespace NetworkFlow

/--
[flowValue_eq_cross](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/MaxFlowMinCut.lean)
-/
@[path]
lemma flowValue_eq_cross
  [Fintype V]
  [DecidableEq V]
  {N : FlowNetwork V}
  {fl : STFlow N}
  {C : STCut N} :
-- imply
  flowValue N fl = (∑ u ∈ C.S, ∑ v ∈ C.Sᶜ, fl.f u v) - (∑ u ∈ C.S, ∑ v ∈ C.Sᶜ, fl.f v u) := by
-- proof
  unfold flowValue
  have hval : ∑ v : V, fl.f N.s v - ∑ v : V, fl.f v N.s =
    ∑ v ∈ C.S, (∑ w : V, fl.f v w - ∑ w : V, fl.f w v) := by
    have hcons : ∀ v ∈ C.S, v ≠ N.s →
      ∑ w : V, fl.f v w - ∑ w : V, fl.f w v = 0 := by
      intro v hv hvs
      have hvt : v ≠ N.t := fun h => C.t_not_mem (h ▸ hv)
      linarith [fl.conservation v hvs hvt]
    rw [← Finset.add_sum_erase C.S _ C.s_mem]
    simp only [Finset.sum_eq_zero (fun v hv => hcons v (Finset.mem_of_mem_erase hv)
      (Finset.ne_of_mem_erase hv)), add_zero]
  have hcross : ∑ v ∈ C.S, (∑ w : V, fl.f v w - ∑ w : V, fl.f w v) =
    (∑ v ∈ C.S, ∑ w ∈ C.Sᶜ, fl.f v w) -
    (∑ v ∈ C.S, ∑ w ∈ C.Sᶜ, fl.f w v) := by
    have split_out : ∀ v, ∑ w : V, fl.f v w =
      ∑ w ∈ C.S, fl.f v w + ∑ w ∈ C.Sᶜ, fl.f v w := by
      intro v; rw [← Finset.sum_add_sum_compl C.S]
    have split_in : ∀ v, ∑ w : V, fl.f w v =
      ∑ w ∈ C.S, fl.f w v + ∑ w ∈ C.Sᶜ, fl.f w v := by
      intro v; rw [← Finset.sum_add_sum_compl C.S]
    simp_rw [split_out, split_in]
    have cancel : ∑ v ∈ C.S, ∑ w ∈ C.S, fl.f v w =
      ∑ v ∈ C.S, ∑ w ∈ C.S, fl.f w v := by
      rw [Finset.sum_comm]
    have h1 : ∑ v ∈ C.S, (∑ w ∈ C.S, fl.f v w + ∑ w ∈ C.Sᶜ, fl.f v w -
      (∑ w ∈ C.S, fl.f w v + ∑ w ∈ C.Sᶜ, fl.f w v)) =
      (∑ v ∈ C.S, ∑ w ∈ C.S, fl.f v w) + (∑ v ∈ C.S, ∑ w ∈ C.Sᶜ, fl.f v w) -
      (∑ v ∈ C.S, ∑ w ∈ C.S, fl.f w v) - (∑ v ∈ C.S, ∑ w ∈ C.Sᶜ, fl.f w v) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      ring
    linarith
  linarith

end NetworkFlow

namespace NetworkFlow

/--
[max_flow_min_cut](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/MaxFlowMinCut.lean)
-/
@[path]
lemma max_flow_min_cut
  [Fintype V]
  [DecidableEq V]
  {N : FlowNetwork V}
  {fl : STFlow N}
-- given
  (hmax : NoAugmentingPath N fl) :
-- imply
  ∃ C : STCut N, flowValue N fl = cutCapacity N C := by
-- proof
  use maxFlowCut N fl hmax
  have heq := flowValue_eq_cross N fl (maxFlowCut N fl hmax)
  rw [heq]
  have hfwd : ∑ u ∈ (maxFlowCut N fl hmax).S, ∑ v ∈ (maxFlowCut N fl hmax).Sᶜ, fl.f u v =
    cutCapacity N (maxFlowCut N fl hmax) := by
    unfold cutCapacity
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    have hu_reach : ResReachable N fl u := by
      rw [maxFlowCut_S] at hu
      exact (mem_resReachableSet_iff N fl u).mp hu
    have hv_not_reach : ¬ ResReachable N fl v := by
      rw [maxFlowCut_S] at hv
      rw [Finset.mem_compl] at hv
      exact fun h => hv ((mem_resReachableSet_iff N fl v).mpr h)
    exact flow_eq_cap_of_cross hu_reach hv_not_reach
  have hbwd : ∑ u ∈ (maxFlowCut N fl hmax).S, ∑ v ∈ (maxFlowCut N fl hmax).Sᶜ, fl.f v u = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro v hv
    have hu_reach : ResReachable N fl u := by
      rw [maxFlowCut_S] at hu
      exact (mem_resReachableSet_iff N fl u).mp hu
    have hv_not_reach : ¬ ResReachable N fl v := by
      rw [maxFlowCut_S] at hv
      rw [Finset.mem_compl] at hv
      exact fun h => hv ((mem_resReachableSet_iff N fl v).mpr h)
    exact flow_eq_zero_of_cross hu_reach hv_not_reach
  linarith

end NetworkFlow

/--
[mem_resReachableSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/MaxFlowMinCut.lean)
-/
@[path]
private lemma mem_resReachableSet_iff_eq
  [Fintype V]
  [DecidableEq V]
  {N : FlowNetwork V}
  {fl : STFlow N}
  {v : V} :
-- imply
  v ∈ resReachableSet N fl ↔ ResReachable N fl v := by
-- proof
  apply NetworkFlow.mem_resReachableSet_iff N fl v

/--
[s_mem_resReachableSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/MaxFlowMinCut.lean)
-/
@[path]
private lemma s_mem_resReachableSet_eq
  [Fintype V]
  [DecidableEq V]
  {N : FlowNetwork V}
  {fl : STFlow N} :
-- imply
  N.s ∈ resReachableSet N fl := by
-- proof
  apply NetworkFlow.s_mem_resReachableSet N fl

/--
[t_not_mem_resReachableSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/MaxFlowMinCut.lean)
-/
@[path]
private lemma t_not_mem_resReachableSet_eq
  [Fintype V]
  [DecidableEq V]
  {N : FlowNetwork V}
  {fl : STFlow N}
-- given
  (hmax : NoAugmentingPath N fl) :
-- imply
  N.t ∉ resReachableSet N fl := by
-- proof
  apply NetworkFlow.t_not_mem_resReachableSet N fl hmax


-- created on 2026-10-23
