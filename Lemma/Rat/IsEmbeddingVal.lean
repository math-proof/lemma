import Mathlib
import sympy.Basic

open NumberField

/--
[NumberField_InfiniteAdeleRing_isEmbedding_units_val](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_NumberField_InfiniteAdeleRing_isEmbedding_units_val.lean)
-/
@[path]
private lemma main
  [Field K] [NumberField K] :
-- imply
  Topology.IsEmbedding (Units.val : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K) := by
-- proof
  refine Units.isEmbedding_val_mk' (f := fun x : InfiniteAdeleRing K => fun w : InfinitePlace K => (x w)⁻¹) ?_ ?_
  · refine continuousOn_pi.2 fun w => ?_
    have hc : ContinuousOn (fun x : InfiniteAdeleRing K => x w) {x : InfiniteAdeleRing K | IsUnit x} := (continuous_apply w).continuousOn
    refine ContinuousOn.inv₀ hc fun x hx => ?_
    obtain ⟨u, rfl⟩ := hx
    exact (u.map (Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) w).toMonoidHom).ne_zero
  · intro u
    funext w
    have h := congrFun u.inv_mul w

    have h' : ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w * ((u : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w = 1 := h
    exact (eq_inv_of_mul_eq_one_left h').symm


-- created on 2026-10-05
