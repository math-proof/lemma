import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingLatticeGreenSpatialDecay
open Filter Set Topology StatMech StatMech.FrontierA


/--
[isingLatticeGreen_eventually_small_outside_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingLatticeGreenSpatialDecay.lean)
-/
@[path]
private lemma isingLatticeGreen_eventually_small_outside_box_eq
  {d : Nat}
  {epsilon : Real}
-- given
  (hd : 2 < d)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ R : Nat, ∀ x : Site d, x ∉ box d R -> := by
-- proof
  apply StatMech.FrontierA.isingLatticeGreen_eventually_small_outside_box hd epsilon hepsilon


-- created on 2026-10-23
