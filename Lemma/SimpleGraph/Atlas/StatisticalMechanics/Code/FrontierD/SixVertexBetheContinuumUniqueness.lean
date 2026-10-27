import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuumUniqueness
open StatMech StatMech.FrontierD


/--
[sixVertexContinuousDensityEquation_unique_of_equal_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuumUniqueness.lean)
-/
@[path]
private lemma sixVertexContinuousDensityEquation_unique_of_equal_mass_eq
  {c : Real}
  {rho sigma : Real -> Real}
-- given
  (hc : 2 < c)
  (hrho : Continuous rho)
  (hsigma : Continuous sigma)
  (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
  (hsigmaEq : SixVertexSatisfiesContinuousDensityEquation c sigma)
  (hmass : (∫ y in -Real.pi..Real.pi, rho y) = ∫ y in -Real.pi..Real.pi, sigma y) :
-- imply
  ∀ x ∈ Set.Icc (-Real.pi) Real.pi, rho x = sigma x := by
-- proof
  apply StatMech.FrontierD.sixVertexContinuousDensityEquation_unique_of_equal_mass hc hrho hsigma hrhoEq hsigmaEq hmass


-- created on 2026-10-23
