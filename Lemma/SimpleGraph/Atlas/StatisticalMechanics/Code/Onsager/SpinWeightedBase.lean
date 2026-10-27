import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SpinWeightedBase
open StatMech StatMech.Onsager


/--
[ons_KWmatWeightedPhase_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedBase.lean)
-/
@[path]
private lemma ons_KWmatWeightedPhase_zero_eq
  {L : ℕ}
  {omega u v : ℂ} :
-- imply
  ons_KWmatWeightedPhase L (fun _ => 0) omega u v = 0 := by
-- proof
  apply StatMech.Onsager.ons_KWmatWeightedPhase_zero L omega u v

/--
[ons_weightedSpinCharacterSum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedBase.lean)
-/
@[path]
private lemma ons_weightedSpinCharacterSum_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2} :
-- imply
  ons_weightedSpinCharacterSum L (fun _ => 0) a b = 1 := by
-- proof
  apply StatMech.Onsager.ons_weightedSpinCharacterSum_zero L a b

/--
[ons_weightedRoot_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedBase.lean)
-/
@[path]
private lemma ons_weightedRoot_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2} :
-- imply
  ons_detWalkRoot (ons_KWmatWeightedPhase L (fun _ => 0) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = ons_weightedSpinCharacterSum L (fun _ => 0) a b := by
-- proof
  apply StatMech.Onsager.ons_weightedRoot_zero L a b


-- created on 2026-10-23
