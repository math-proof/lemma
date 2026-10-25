import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleCut.Part5
open StatMech StatMech.FrontierD


/--
[sixVertexFinPrefixIndex_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleCut.lean)
-/
@[path]
private lemma sixVertexFinPrefixIndex_val_eq
  {N : Nat}
  {cut : Fin N}
  {i : Fin cut.val} :
-- imply
  (sixVertexFinPrefixIndex cut i).val = i.val := by
-- proof
  apply StatMech.FrontierD.sixVertexFinPrefixIndex_val cut i

/--
[sixVertexFinSuffixIndex_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleCut.lean)
-/
@[path]
private lemma sixVertexFinSuffixIndex_val_eq
  {N : Nat}
  {cut : Fin N}
  {i : Fin (N - cut.val)} :
-- imply
  (sixVertexFinSuffixIndex cut i).val = cut.val + i.val := by
-- proof
  apply StatMech.FrontierD.sixVertexFinSuffixIndex_val cut i

/--
[sixVertexFinPrefixIndex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleCut.lean)
-/
@[path]
private lemma sixVertexFinPrefixIndex_injective_eq
  {N : Nat}
  {cut : Fin N} :
-- imply
  Function.Injective (sixVertexFinPrefixIndex cut) := by
-- proof
  apply StatMech.FrontierD.sixVertexFinPrefixIndex_injective cut

/--
[sixVertexFinSuffixIndex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleCut.lean)
-/
@[path]
private lemma sixVertexFinSuffixIndex_injective_eq
  {N : Nat}
  {cut : Fin N} :
-- imply
  Function.Injective (sixVertexFinSuffixIndex cut) := by
-- proof
  apply StatMech.FrontierD.sixVertexFinSuffixIndex_injective cut

/--
[sixVertexFinPrefixIndex_ne_suffixIndex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleCut.lean)
-/
@[path]
private lemma sixVertexFinPrefixIndex_ne_suffixIndex_eq
  {N : Nat}
  {cut : Fin N}
  {i : Fin cut.val}
  {j : Fin (N - cut.val)} :
-- imply
  sixVertexFinPrefixIndex cut i ≠ sixVertexFinSuffixIndex cut j := by
-- proof
  apply StatMech.FrontierD.sixVertexFinPrefixIndex_ne_suffixIndex cut i j

/--
[sixVertexDegreeTwoStrandCycleForward_finish_eq_backward_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleCut.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandCycleForward_finish_eq_backward_start_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
  {cut : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm homega heta hdegree seed))}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hcut : 0 < cut.val) :
-- imply
  (sixVertexDegreeTwoStrandCycleForwardArc homega heta hdegree seed cut hcut).finish = (sixVertexDegreeTwoStrandCycleBackwardArc homega heta hdegree seed cut).start := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandCycleForward_finish_eq_backward_start homega heta hdegree seed cut hcut

/--
[sixVertexDegreeTwoStrandCycleBackward_finish_eq_forward_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleCut.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandCycleBackward_finish_eq_forward_start_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
  {cut : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm homega heta hdegree seed))}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hcut : 0 < cut.val) :
-- imply
  (sixVertexDegreeTwoStrandCycleBackwardArc homega heta hdegree seed cut).finish = (sixVertexDegreeTwoStrandCycleForwardArc homega heta hdegree seed cut hcut).start := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandCycleBackward_finish_eq_forward_start homega heta hdegree seed cut hcut

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveIndex_val_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleCut.lean)
-/
@[path]
private lemma nextPositiveIndex_val_pos_eq
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
  0 < (seed.nextPositiveIndex hsame).val := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveIndex_val_pos seed hsame


-- created on 2026-10-23
