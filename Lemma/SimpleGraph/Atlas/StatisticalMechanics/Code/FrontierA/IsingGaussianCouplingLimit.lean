import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingGaussianCouplingLimit
open Filter Topology StatMech StatMech.FrontierA


/--
[log_sq_div_dimensionPower_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCouplingLimit.lean)
-/
@[path]
private lemma log_sq_div_dimensionPower_tendsto_zero_eq
  {d : Nat}
  {C : Real}
-- given
  (hd : 4 < d) :
-- imply
  Tendsto (fun x : Real => C ^ 2 * Real.log (x ^ 2) ^ 2 / x ^ (d - 4)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.log_sq_div_dimensionPower_tendsto_zero d hd C

/--
[renormalizedCoupling_tendsto_zero_of_treeDiagram_infrared](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCouplingLimit.lean)
-/
@[path]
private lemma renormalizedCoupling_tendsto_zero_of_treeDiagram_infrared_eq
  {d : Nat}
  {C : Real}
-- given
  (hd : 4 < d)
  (xi chi coupling : Nat -> Real)
  (hxi : Tendsto xi atTop atTop)
  (hchi : ∀ᶠ n in atTop, 0 <= chi n /\ chi n <= C * xi n ^ 2 * Real.log (xi n ^ 2))
  (htree : forall n, 0 <= coupling n /\ coupling n <= chi n ^ 2 / xi n ^ d) :
-- imply
  Tendsto coupling atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.renormalizedCoupling_tendsto_zero_of_treeDiagram_infrared d hd C xi chi coupling hxi hchi htree


-- created on 2026-10-23
