import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailLimit.Part3
open StatMech StatMech.FrontierD


/--
[sixVertexTailConvolutionError_fourWidth_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailLimit.lean)
-/
@[path]
private lemma sixVertexTailConvolutionError_fourWidth_pos_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  0 < sixVertexTailConvolutionError c (sixVertexFourWidth 0 k) := by
-- proof
  apply StatMech.FrontierD.sixVertexTailConvolutionError_fourWidth_pos hc htail k

/--
[cauchySeq_sixVertexSelectedWeightedDensityMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailLimit.lean)
-/
@[path]
private lemma cauchySeq_sixVertexSelectedWeightedDensityMap_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  CauchySeq (sixVertexSelectedWeightedDensityMap hc) := by
-- proof
  apply StatMech.FrontierD.cauchySeq_sixVertexSelectedWeightedDensityMap hc htail

/--
[tendsto_sixVertexSelectedWeightedDensityMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexSelectedWeightedDensityMap_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Tendsto (sixVertexSelectedWeightedDensityMap hc) atTop (nhds (sixVertexTailWeightedDensityLimitMap hc htail)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexSelectedWeightedDensityMap hc htail

/--
[continuous_sixVertexTailRootDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailLimit.lean)
-/
@[path]
private lemma continuous_sixVertexTailRootDensity_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Continuous (sixVertexTailRootDensity hc htail) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexTailRootDensity hc htail

/--
[sixVertexRootDensityWeight_mul_tailRootDensity_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailLimit.lean)
-/
@[path]
private lemma sixVertexRootDensityWeight_mul_tailRootDensity_of_mem_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  sixVertexRootDensityWeight c x * sixVertexTailRootDensity hc htail x = sixVertexTailWeightedDensityLimitMap hc htail ⟨x, hx⟩ := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityWeight_mul_tailRootDensity_of_mem hc htail hx

/--
[tendsto_sixVertexSelectedWeightedDensity_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexSelectedWeightedDensity_at_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  Tendsto (fun k => sixVertexRootDensityWeight c x * sixVertexSelectedFiniteRootDensity hc k x) atTop (nhds (sixVertexRootDensityWeight c x * sixVertexTailRootDensity hc htail x)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexSelectedWeightedDensity_at hc htail hx


-- created on 2026-10-23
