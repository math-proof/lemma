import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.CombinatorialOptimization.code.Flow.FlowCutBound
open Finset BigOperators NetworkFlow


namespace NetworkFlow

/--
[flow_le_cut](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/FlowCutBound.lean)
-/
@[path]
lemma flow_le_cut
  [Fintype V]
  [DecidableEq V]
  {N : FlowNetwork V}
  {fl : STFlow N}
  {C : STCut N} :
-- imply
  flowValue N fl ≤ cutCapacity N C := by
-- proof
  have hval : flowValue N fl =
    ∑ v ∈ C.S, (∑ w : V, fl.f v w - ∑ w : V, fl.f w v) := by
    unfold flowValue
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
  rw [hval, hcross]
  have h_nonneg_back : 0 ≤ ∑ v ∈ C.S, ∑ w ∈ C.Sᶜ, fl.f w v := by
    apply Finset.sum_nonneg
    intro v _
    apply Finset.sum_nonneg
    intro w _
    exact fl.flow_nonneg w v
  have h_flow_le_cap : ∑ v ∈ C.S, ∑ w ∈ C.Sᶜ, fl.f v w ≤ cutCapacity N C := by
    unfold cutCapacity
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    exact fl.flow_cap u v
  linarith

end NetworkFlow


-- created on 2026-10-23
