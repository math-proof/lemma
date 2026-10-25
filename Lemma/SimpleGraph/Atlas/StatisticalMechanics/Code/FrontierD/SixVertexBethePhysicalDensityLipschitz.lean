import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalDensityLipschitz
open StatMech StatMech.FrontierD


/--
[tendsto_sixVertexHalfFilledFiniteRootDensity_at_fourierPhysical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalDensityLipschitz.lean)
-/
@[path]
private lemma tendsto_sixVertexHalfFilledFiniteRootDensity_at_fourierPhysical_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  Tendsto (fun k => sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k) x) atTop (nhds (sixVertexFourierPhysicalDensity c hc x)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexHalfFilledFiniteRootDensity_at_fourierPhysical hc htail hx

/--
[sixVertexFourierPhysicalDensity_lipschitzOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalDensityLipschitz.lean)
-/
@[path]
private lemma sixVertexFourierPhysicalDensity_lipschitzOn_eq
  {c : Real}
  {x z : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hz : z ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  |sixVertexFourierPhysicalDensity c hc x - sixVertexFourierPhysicalDensity c hc z| <= (sixVertexFiniteRootDensityLipschitzConstant c : Real) * |x - z| := by
-- proof
  apply StatMech.FrontierD.sixVertexFourierPhysicalDensity_lipschitzOn hc htail hx hz

/--
[sixVertexTailFiniteDensityFloor_le_fourierPhysicalDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalDensityLipschitz.lean)
-/
@[path]
private lemma sixVertexTailFiniteDensityFloor_le_fourierPhysicalDensity_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  sixVertexTailFiniteDensityFloor c <= sixVertexFourierPhysicalDensity c hc x := by
-- proof
  apply StatMech.FrontierD.sixVertexTailFiniteDensityFloor_le_fourierPhysicalDensity hc htail hx

/--
[sixVertexFourierPhysicalDensity_reciprocal_lipschitzOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalDensityLipschitz.lean)
-/
@[path]
private lemma sixVertexFourierPhysicalDensity_reciprocal_lipschitzOn_eq
  {c : Real}
  {x z : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hz : z ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  |1 / sixVertexFourierPhysicalDensity c hc x - 1 / sixVertexFourierPhysicalDensity c hc z| <= (sixVertexFiniteRootDensityLipschitzConstant c : Real) / sixVertexTailFiniteDensityFloor c ^ 2 * |x - z| := by
-- proof
  apply StatMech.FrontierD.sixVertexFourierPhysicalDensity_reciprocal_lipschitzOn hc htail hx hz


-- created on 2026-10-23
