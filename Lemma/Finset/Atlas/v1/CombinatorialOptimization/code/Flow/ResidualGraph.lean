import Mathlib
import sympy.Basic
import Def.v1.Atlas.CombinatorialOptimization.code.Flow.ResidualGraph.Part2
open Finset BigOperators NetworkFlow


namespace NetworkFlow

/--
[resAdj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/ResidualGraph.lean)
-/
@[path]
lemma resAdj_iff
  [Fintype V]
  [DecidableEq V]
  {N : FlowNetwork V}
  {fl : STFlow N}
  {u v : V} :
-- imply
  resAdj N fl u v ↔ (N.cap u v - fl.f u v > 0 ∨ fl.f v u > 0) := by
-- proof
  unfold resAdj resCap
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    linarith [hc.1, hc.2, fl.flow_cap u v, fl.flow_nonneg v u]
  · intro h
    cases h with
    | inl h => linarith [fl.flow_nonneg v u]
    | inr h => linarith [fl.flow_cap u v, N.cap_nonneg u v]

end NetworkFlow

namespace NetworkFlow

/--
[augmentingPath_iff_residualPath'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/ResidualGraph.lean)
-/
@[path]
lemma augmentingPath_iff_residualPath'
  [Fintype V]
  [DecidableEq V]
  {N : FlowNetwork V}
  {fl : STFlow N}
  {p : List V} :
-- imply
  IsOriginalAugmentingPath N fl p ↔ IsDirectedPath (resAdj N fl) N.s N.t p := by
-- proof
  unfold IsOriginalAugmentingPath IsDirectedPath
  have chain_iff : p.Chain' (fun u v => N.cap u v - fl.f u v > 0 ∨ fl.f v u > 0) ↔
    (∀ i : ℕ, (hi : i + 1 < p.length) →
      resAdj N fl (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, hi⟩)) := by
    rw [show p.Chain' _ = p.IsChain _ from rfl, List.isChain_iff_getElem]
    constructor
    · intro h i hi
      rw [resAdj_iff]
      exact h i hi
    · intro h i hi
      rw [← resAdj_iff]
      exact h i hi
  constructor
  · rintro ⟨hhead, hlast, hlen, hchain, hnodup⟩
    exact ⟨hlen, hhead, hlast, hnodup, chain_iff.mp hchain⟩
  · rintro ⟨hlen, hhead, hlast, hnodup, hadj⟩
    exact ⟨hhead, hlast, hlen, chain_iff.mpr hadj, hnodup⟩

end NetworkFlow

/--
[resCap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/ResidualGraph.lean)
-/
@[path]
private lemma resCap_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {N : FlowNetwork V}
  {fl : STFlow N}
  {u v : V} :
-- imply
  0 ≤ resCap N fl u v := by
-- proof
  apply NetworkFlow.resCap_nonneg N fl u v


-- created on 2026-10-23
