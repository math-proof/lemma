import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
open Finset StatMech StatMech.FrontierD


/--
[sixVertexArrowsComplement_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalParticleHole.lean)
-/
@[path]
private lemma sixVertexArrowsComplement_horizontal_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {v : T.Vertex} :
-- imply
  (sixVertexArrowsComplement omega).horizontal v = !omega.horizontal v := by
-- proof
  apply StatMech.FrontierD.sixVertexArrowsComplement_horizontal omega v

/--
[sixVertexArrowsComplement_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalParticleHole.lean)
-/
@[path]
private lemma sixVertexArrowsComplement_vertical_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {v : T.Vertex} :
-- imply
  (sixVertexArrowsComplement omega).vertical v = !omega.vertical v := by
-- proof
  apply StatMech.FrontierD.sixVertexArrowsComplement_vertical omega v

/--
[sixVertexArrowsComplement_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalParticleHole.lean)
-/
@[path]
private lemma sixVertexArrowsComplement_complement_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T} :
-- imply
  sixVertexArrowsComplement (sixVertexArrowsComplement omega) = omega := by
-- proof
  apply StatMech.FrontierD.sixVertexArrowsComplement_complement omega

/--
[sixVertexArrowsComplement_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalParticleHole.lean)
-/
@[path]
private lemma sixVertexArrowsComplement_injective_eq
  {T : EvenTorus} :
-- imply
  Function.Injective (@sixVertexArrowsComplement T) := by
-- proof
  apply StatMech.FrontierD.sixVertexArrowsComplement_injective

/--
[sixVertexArrowsComplement_iceRule](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalParticleHole.lean)
-/
@[path]
private lemma sixVertexArrowsComplement_iceRule_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
-- given
  (homega : omega.IceRule) :
-- imply
  (sixVertexArrowsComplement omega).IceRule := by
-- proof
  apply StatMech.FrontierD.sixVertexArrowsComplement_iceRule homega

/--
[sixVertexArrowsComplement_isCType_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalParticleHole.lean)
-/
@[path]
private lemma sixVertexArrowsComplement_isCType_iff_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {v : T.Vertex} :
-- imply
  (sixVertexArrowsComplement omega).IsCType v ↔ omega.IsCType v := by
-- proof
  apply StatMech.FrontierD.sixVertexArrowsComplement_isCType_iff omega v

/--
[sixVertexArrowsComplement_cTypeCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalParticleHole.lean)
-/
@[path]
private lemma sixVertexArrowsComplement_cTypeCount_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T} :
-- imply
  sixVertexTorusCTypeCount (sixVertexArrowsComplement omega) = sixVertexTorusCTypeCount omega := by
-- proof
  apply StatMech.FrontierD.sixVertexArrowsComplement_cTypeCount omega

/--
[sixVertexUpCount_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalParticleHole.lean)
-/
@[path]
private lemma sixVertexUpCount_complement_eq
  {N : Nat}
  {row : SixVertexRow N} :
-- imply
  sixVertexUpCount (fun i => !row i) = N - sixVertexUpCount row := by
-- proof
  apply StatMech.FrontierD.sixVertexUpCount_complement row

/--
[sixVertexPhysicalParticleHoleMiddle_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalParticleHole.lean)
-/
@[path]
private lemma sixVertexPhysicalParticleHoleMiddle_pos_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_lt : middle.val < T.width) :
-- imply
  0 < (sixVertexPhysicalParticleHoleMiddle middle).val := by
-- proof
  apply StatMech.FrontierD.sixVertexPhysicalParticleHoleMiddle_pos middle hmiddle_lt

/--
[sixVertexPhysicalParticleHoleMiddle_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalParticleHole.lean)
-/
@[path]
private lemma sixVertexPhysicalParticleHoleMiddle_lt_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val) :
-- imply
  (sixVertexPhysicalParticleHoleMiddle middle).val < T.width := by
-- proof
  apply StatMech.FrontierD.sixVertexPhysicalParticleHoleMiddle_lt middle hmiddle_pos

/--
[sixVertexPhysicalParticleHoleSourceEmbedding_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalParticleHole.lean)
-/
@[path]
private lemma sixVertexPhysicalParticleHoleSourceEmbedding_totalC_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {source : SixVertexConfigurationPhysicalSource T (sixVertexPhysicalParticleHoleMiddle middle) (sixVertexPhysicalParticleHoleMiddle_pos middle hmiddle_lt) (sixVertexPhysicalParticleHoleMiddle_lt middle hmiddle_pos)} :
-- imply
  sixVertexConfigurationPairTotalCPhysical (sixVertexPhysicalParticleHoleSourceEmbedding (middle := middle) (hmiddle_pos := hmiddle_pos) (hmiddle_lt := hmiddle_lt) source) = sixVertexConfigurationPairTotalCPhysical source := by
-- proof
  apply StatMech.FrontierD.sixVertexPhysicalParticleHoleSourceEmbedding_totalC source

/--
[sixVertexPhysicalParticleHoleTargetEmbedding_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalParticleHole.lean)
-/
@[path]
private lemma sixVertexPhysicalParticleHoleTargetEmbedding_totalC_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {target : SixVertexConfigurationPhysicalTarget T middle} :
-- imply
  sixVertexConfigurationPairTotalCPhysical (sixVertexPhysicalParticleHoleTargetEmbedding target) = sixVertexConfigurationPairTotalCPhysical target := by
-- proof
  apply StatMech.FrontierD.sixVertexPhysicalParticleHoleTargetEmbedding_totalC target


-- created on 2026-10-23
