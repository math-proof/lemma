module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic.Part4
open Finset BigOperators CoxeterGroup
open scoped Topology


public section

namespace TitsCone

/--
[continuous_pairing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeCorollary.lean)
-/
@[path]
private theorem main
  [DecidableEq B]
  [Fintype B]
  {α : B → ℝ} :
-- imply
  Continuous (fun x : B → ℝ => pairing α x) := by
-- proof
  unfold pairing
  apply continuous_finsetSum
  intro s _
  exact continuous_const.mul (continuous_apply s)

end TitsCone


-- created on 2026-10-23
-- updated on 2026-10-26
