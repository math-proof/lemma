import Mathlib
import sympy.Basic

open Topology

/--
[Submodule_finiteDimensional_of_isCompactOperator_of_forall_apply_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Submodule_finiteDimensional_of_isCompactOperator_of_forall_apply_eq.lean)
-/
@[main]
private lemma main
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {T : E →L[𝕜] E}
  {V : Submodule 𝕜 E}
-- given
  (hT : IsCompactOperator T)
  (hV : ∀ v ∈ V, T v = v) :
-- imply
  FiniteDimensional 𝕜 ↥V := by
-- proof
  let W : Submodule 𝕜 E := LinearMap.ker ((T : E →ₗ[𝕜] E) - LinearMap.id)
  have hWmem : ∀ v : E, v ∈ W ↔ T v = v := by
    intro v
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  have hVW : V ≤ W := fun v hv => (hWmem v).mpr (hV v hv)
  have hWclosed : IsClosed (W : Set E) := by
    have : (W : Set E) = {v | T v = v} := Set.ext fun v => hWmem v
    rw [this]
    exact isClosed_eq T.continuous continuous_id

  haveI : FiniteDimensional 𝕜 ↥W := by
    refine FiniteDimensional.of_isCompact_closedBall₀ 𝕜 zero_lt_one ?_
    have hK : IsCompact (closure ((T : E → E) '' Metric.closedBall 0 1)) := by
      have h := hT.isCompact_closure_image_ball (f := (T : E →ₗ[𝕜] E)) 2
      exact h.of_isClosed_subset isClosed_closure
        (closure_mono (Set.image_mono (Metric.closedBall_subset_ball (by norm_num))))
    have hemb : Topology.IsClosedEmbedding (Subtype.val : ↥W → E) :=
      hWclosed.isClosedEmbedding_subtypeVal
    rw [hemb.isCompact_iff]
    refine hK.of_isClosed_subset (hemb.isClosedMap _ Metric.isClosed_closedBall) ?_
    rintro _ ⟨w, hw, rfl⟩
    refine subset_closure ⟨(w : E), ?_, ((hWmem w).mp w.2)⟩
    simpa using hw
  exact Submodule.finiteDimensional_of_le hVW


-- created on 2026-10-05
