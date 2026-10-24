import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierDensity
open Filter Topology StatMech StatMech.FrontierD


/--
[summable_sixVertexFourierRootDensityMajorant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierDensity.lean)
-/
@[path]
private lemma summable_sixVertexFourierRootDensityMajorant_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Summable (sixVertexFourierRootDensityMajorant lam) := by
-- proof
  apply StatMech.FrontierD.summable_sixVertexFourierRootDensityMajorant hlam

/--
[norm_sixVertexFourierRootDensityTerm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierDensity.lean)
-/
@[path]
private lemma norm_sixVertexFourierRootDensityTerm_le_eq
  {lam : Real}
  {n : Nat}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  ‖sixVertexFourierRootDensityTerm lam n alpha‖ <= sixVertexFourierRootDensityMajorant lam n := by
-- proof
  apply StatMech.FrontierD.norm_sixVertexFourierRootDensityTerm_le hlam n alpha

/--
[summable_sixVertexFourierRootDensityTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierDensity.lean)
-/
@[path]
private lemma summable_sixVertexFourierRootDensityTerm_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Summable (fun n => sixVertexFourierRootDensityTerm lam n alpha) := by
-- proof
  apply StatMech.FrontierD.summable_sixVertexFourierRootDensityTerm hlam alpha

/--
[continuous_sixVertexFourierRootDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierDensity.lean)
-/
@[path]
private lemma continuous_sixVertexFourierRootDensity_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Continuous (sixVertexFourierRootDensity lam) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexFourierRootDensity hlam

/--
[intervalIntegral_sixVertexFourierRootDensityTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierDensity.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexFourierRootDensityTerm_eq
  {lam : Real}
  {n : Nat} :
-- imply
  ∫ alpha in -Real.pi..Real.pi, sixVertexFourierRootDensityTerm lam n alpha = 0 := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexFourierRootDensityTerm lam n

/--
[intervalIntegral_tsum_sixVertexFourierRootDensityTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierDensity.lean)
-/
@[path]
private lemma intervalIntegral_tsum_sixVertexFourierRootDensityTerm_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  ∫ alpha in -Real.pi..Real.pi, (∑' n : Nat, sixVertexFourierRootDensityTerm lam n alpha) = 0 := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_tsum_sixVertexFourierRootDensityTerm hlam

/--
[intervalIntegral_sixVertexFourierRootDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierDensity.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexFourierRootDensity_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  ∫ alpha in -Real.pi..Real.pi, sixVertexFourierRootDensity lam alpha = Real.pi := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexFourierRootDensity hlam


-- created on 2026-10-23
