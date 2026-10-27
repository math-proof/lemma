import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRapidityMomentum.Part3
open StatMech StatMech.FrontierD


/--
[sixVertexXiFourier_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityMomentum.lean)
-/
@[path]
private lemma sixVertexXiFourier_pos_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  0 < sixVertexXiFourier lam alpha := by
-- proof
  apply StatMech.FrontierD.sixVertexXiFourier_pos hlam alpha

/--
[sixVertexXiFourier_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityMomentum.lean)
-/
@[path]
private lemma sixVertexXiFourier_neg_eq
  {lam alpha : Real} :
-- imply
  sixVertexXiFourier lam (-alpha) = sixVertexXiFourier lam alpha := by
-- proof
  apply StatMech.FrontierD.sixVertexXiFourier_neg lam alpha

/--
[intervalIntegral_zero_pi_sixVertexXiFourierTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityMomentum.lean)
-/
@[path]
private lemma intervalIntegral_zero_pi_sixVertexXiFourierTerm_eq
  {lam : Real}
  {n : Nat} :
-- imply
  (∫ alpha in (0 : Real)..Real.pi, sixVertexXiFourierTerm lam n alpha) = 0 := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_zero_pi_sixVertexXiFourierTerm lam n

/--
[intervalIntegral_zero_pi_sixVertexXiFourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityMomentum.lean)
-/
@[path]
private lemma intervalIntegral_zero_pi_sixVertexXiFourier_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  (∫ alpha in (0 : Real)..Real.pi, sixVertexXiFourier lam alpha) = Real.pi := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_zero_pi_sixVertexXiFourier hlam

/--
[hasDerivAt_sixVertexRapidityMomentum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityMomentum.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexRapidityMomentum_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  HasDerivAt (sixVertexRapidityMomentum lam) (sixVertexXiFourier lam alpha) alpha := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexRapidityMomentum hlam alpha

/--
[strictMono_sixVertexRapidityMomentum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityMomentum.lean)
-/
@[path]
private lemma strictMono_sixVertexRapidityMomentum_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  StrictMono (sixVertexRapidityMomentum lam) := by
-- proof
  apply StatMech.FrontierD.strictMono_sixVertexRapidityMomentum hlam

/--
[sixVertexRapidityMomentum_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityMomentum.lean)
-/
@[path]
private lemma sixVertexRapidityMomentum_pi_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  sixVertexRapidityMomentum lam Real.pi = Real.pi := by
-- proof
  apply StatMech.FrontierD.sixVertexRapidityMomentum_pi hlam

/--
[sixVertexRapidityMomentum_neg_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityMomentum.lean)
-/
@[path]
private lemma sixVertexRapidityMomentum_neg_pi_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  sixVertexRapidityMomentum lam (-Real.pi) = -Real.pi := by
-- proof
  apply StatMech.FrontierD.sixVertexRapidityMomentum_neg_pi hlam

/--
[sixVertexRapidityMomentum_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityMomentum.lean)
-/
@[path]
private lemma sixVertexRapidityMomentum_mem_Icc_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam)
  (halpha : alpha ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  sixVertexRapidityMomentum lam alpha ∈ Set.Icc (-Real.pi) Real.pi := by
-- proof
  apply StatMech.FrontierD.sixVertexRapidityMomentum_mem_Icc hlam halpha


-- created on 2026-10-23
