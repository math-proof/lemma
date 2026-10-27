import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationWalkSign
open StatMech StatMech.Onsager


/--
[ons_loopWeight_eq_edgeWeight_neZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkSign.lean)
-/
@[path]
private lemma ons_loopWeight_eq_edgeWeight_neZero_eq
  [Fintype E]
  [DecidableEq E]
  {Lambda : Matrix E E ℂ}
  {n : ℕ}
  [NeZero n]
  {v : Fin n → E} :
-- imply
  ons_loopWeight Lambda v = ons_edgeWeight Lambda (List.ofFn v ++ [v 0]) := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_eq_edgeWeight_neZero Lambda v

/--
[ons_decCycleFirstReturn_edgeWeight_eq_loopWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkSign.lean)
-/
@[path]
private lemma ons_decCycleFirstReturn_edgeWeight_eq_loopWeight_eq
  {L : ℕ}
  [NeZero L]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {Lambda : Matrix (ons_Dart L) (ons_Dart L) ℂ} :
-- imply
  ons_edgeWeight Lambda (ons_decCycleFirstReturn q) = ons_loopWeight Lambda (ons_decCycleDartLoop q) := by
-- proof
  apply StatMech.Onsager.ons_decCycleFirstReturn_edgeWeight_eq_loopWeight q Lambda

/--
[ons_firstReturnWeight_decCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkSign.lean)
-/
@[path]
private lemma ons_firstReturnWeight_decCycle_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {Lambda : Matrix (ons_Dart L) (ons_Dart L) ℂ}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ons_firstReturnWeight Lambda d (ons_dartRev L d) (ons_decCycleFirstReturn q) = ons_edgeWeight Lambda (ons_decCycleFirstReturn q) := by
-- proof
  apply StatMech.Onsager.ons_firstReturnWeight_decCycle q hq hsnd Lambda

/--
[ons_decCycleFirstReturn_unitWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkSign.lean)
-/
@[path]
private lemma ons_decCycleFirstReturn_unitWeight_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {omega : ℂ}
  {a b : Fin 2}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ons_edgeWeight (ons_KWmatWeightedPhase L (fun _ => 1) omega (ons_spinPhase L a) (ons_spinPhase L b)) (ons_decCycleFirstReturn q) = ons_spinLinearCharacter a b (ons_evenHomology L (ons_walkOriginalEdges q)) * ∏ k, ons_turnW omega (ons_decCycleDartLoop q (k + 1)).2 (ons_decCycleDartLoop q k).2 := by
-- proof
  apply StatMech.Onsager.ons_decCycleFirstReturn_unitWeight q hq hsnd omega a b

/--
[ons_decCycleFirstReturn_weight_eq_spinCharacter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkSign.lean)
-/
@[path]
private lemma ons_decCycleFirstReturn_weight_eq_spinCharacter_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {a b : Fin 2}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d)
  (hturn : (∏ k, ons_turnW ons_turnRoot (ons_decCycleDartLoop q (k + 1)).2 (ons_decCycleDartLoop q k).2) = -(ons_spinCharacter 0 0 (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ)) :
-- imply
  ons_edgeWeight (ons_KWmatWeightedPhase L weight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) (ons_decCycleFirstReturn q) = -(ons_spinCharacter a b (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) * ∏ edge ∈ ons_walkOriginalEdges q, weight edge := by
-- proof
  apply StatMech.Onsager.ons_decCycleFirstReturn_weight_eq_spinCharacter q hq hsnd weight a b hturn


-- created on 2026-10-23
