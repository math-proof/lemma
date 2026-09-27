import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Flow
import sympy.dynamics.actor_critic
import sympy.Basic
open Filter


@[main]
private lemma main
  {α : Type*} [TopologicalSpace α]
-- given
  (Φ : ContinuousSemiflow α)
  (K : Set α) :
-- imply
  IsForwardInvariant Φ.toFun (omegaLimit atTop Φ.toFun K) := by
-- proof
  intro t ht y hy
  have h : Set.MapsTo (Φ.toFun t) (omegaLimit atTop Φ.toFun K) (omegaLimit atTop (fun s => Φ.toFun (t + s)) K) :=
    mapsTo_omegaLimit' K (Set.mapsTo_id K) ((eventually_ge_atTop 0).mono fun s hs x _ => (Φ.map_add' t s ht hs x).symm) (Φ.continuous_apply t ht)
  exact omegaLimit_subset_of_tendsto Φ.toFun K (tendsto_atTop_add_const_left atTop t tendsto_id) (h hy)


-- created on 2026-09-26
