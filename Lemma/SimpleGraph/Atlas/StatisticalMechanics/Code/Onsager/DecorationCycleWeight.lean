import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.DecorationCycleWeight
open StatMech StatMech.Onsager


/--
[ons_decCycleFirstReturn_weight_eq_neg_spinCharacter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleWeight.lean)
-/
@[path]
private lemma ons_decCycleFirstReturn_weight_eq_neg_spinCharacter_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {a b : Fin 2}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ons_edgeWeight (ons_KWmatWeightedPhase L weight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) (ons_decCycleFirstReturn q) = -(ons_spinCharacter a b (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) * ∏ edge ∈ ons_walkOriginalEdges q, weight edge := by
-- proof
  apply StatMech.Onsager.ons_decCycleFirstReturn_weight_eq_neg_spinCharacter q hq hsnd weight a b

/--
[ons_firstReturnWeight_decCycle_eq_neg_spinCharacter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleWeight.lean)
-/
@[path]
private lemma ons_firstReturnWeight_decCycle_eq_neg_spinCharacter_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {a b : Fin 2}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ons_firstReturnWeight (ons_KWmatWeightedPhase L weight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) d (ons_dartRev L d) (ons_decCycleFirstReturn q) = -(ons_spinCharacter a b (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) * ∏ edge ∈ ons_walkOriginalEdges q, weight edge := by
-- proof
  apply StatMech.Onsager.ons_firstReturnWeight_decCycle_eq_neg_spinCharacter q hq hsnd weight a b


-- created on 2026-10-23
