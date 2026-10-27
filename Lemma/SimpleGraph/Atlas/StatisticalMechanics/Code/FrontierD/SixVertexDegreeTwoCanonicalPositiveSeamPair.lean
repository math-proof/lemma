import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalPositiveSeamPair.Part5
open StatMech StatMech.FrontierD


/--
[sixVertexDegreeTwoStrandCycleEnumeration_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalPositiveSeamPair.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandCycleEnumeration_zero_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed (sixVertexDegreeTwoStrandCycleZeroIndex homega heta hdegree seed) = seed := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandCycleEnumeration_zero homega heta hdegree seed

/--
[sixVertexDegreeTwoStrandCycleEnumeration_position](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalPositiveSeamPair.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandCycleEnumeration_position_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed dart : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree).SameCycle seed dart) :
-- imply
  sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed (sixVertexDegreeTwoStrandCyclePosition homega heta hdegree seed dart hsame) = dart := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandCycleEnumeration_position homega heta hdegree seed dart hsame

/--
[sixVertexDegreeTwoStrandCyclePosition_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalPositiveSeamPair.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandCyclePosition_ne_zero_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed dart : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree).SameCycle seed dart)
  (hne : seed ≠ dart) :
-- imply
  sixVertexDegreeTwoStrandCyclePosition homega heta hdegree seed dart hsame ≠ sixVertexDegreeTwoStrandCycleZeroIndex homega heta hdegree seed := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandCyclePosition_ne_zero homega heta hdegree seed dart hsame hne

/--
[sixVertexDegreeTwoStrandPositiveNonzeroIndices_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalPositiveSeamPair.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandPositiveNonzeroIndices_nonempty_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed dart : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree).SameCycle seed dart)
  (hne : seed ≠ dart)
  (hpositive : sixVertexDegreeTwoStrandStepSeamSign hdegree dart = 1) :
-- imply
  (sixVertexDegreeTwoStrandPositiveNonzeroIndices homega heta hdegree seed).Nonempty := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandPositiveNonzeroIndices_nonempty homega heta hdegree seed dart hsame hne hpositive

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveIndex_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalPositiveSeamPair.lean)
-/
@[path]
private lemma nextPositiveIndex_mem_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
-- given
  (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree).SameCycle seed.first seed.second) :
-- imply
  seed.nextPositiveIndex hsame ∈ sixVertexDegreeTwoStrandPositiveNonzeroIndices homega heta hdegree seed.first := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveIndex_mem seed hsame

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveIndex_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalPositiveSeamPair.lean)
-/
@[path]
private lemma nextPositiveIndex_ne_zero_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
-- given
  (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree).SameCycle seed.first seed.second) :
-- imply
  seed.nextPositiveIndex hsame ≠ sixVertexDegreeTwoStrandCycleZeroIndex homega heta hdegree seed.first := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveIndex_ne_zero seed hsame

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveIndex_minimal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalPositiveSeamPair.lean)
-/
@[path]
private lemma nextPositiveIndex_minimal_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {i : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm homega heta hdegree seed.first))}
-- given
  (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree).SameCycle seed.first seed.second)
  (hi : i ≠ sixVertexDegreeTwoStrandCycleZeroIndex homega heta hdegree seed.first)
  (hpositive : sixVertexDegreeTwoStrandStepSeamSign hdegree (sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed.first i) = 1) :
-- imply
  seed.nextPositiveIndex hsame ≤ i := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveIndex_minimal seed hsame i hi hpositive

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveDart_seamSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalPositiveSeamPair.lean)
-/
@[path]
private lemma nextPositiveDart_seamSign_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
-- given
  (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree).SameCycle seed.first seed.second) :
-- imply
  sixVertexDegreeTwoStrandStepSeamSign hdegree (seed.nextPositiveDart hsame) = 1 := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveDart_seamSign seed hsame

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.first_ne_nextPositiveDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalPositiveSeamPair.lean)
-/
@[path]
private lemma first_ne_nextPositiveDart_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
-- given
  (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree).SameCycle seed.first seed.second) :
-- imply
  seed.first ≠ seed.nextPositiveDart hsame := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.first_ne_nextPositiveDart seed hsame


-- created on 2026-10-23
