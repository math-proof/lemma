import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[KWStraightLineEmbedding.dartVector_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStraightLineEmbedding.lean)
-/
@[path]
private lemma dartVector_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {dart : G.Dart} :
-- imply
  embedding.vertex dart.snd - embedding.vertex dart.fst ≠ 0 := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.dartVector_ne_zero embedding dart

/--
[KWStraightLineEmbedding.dartAngle_sub_eq_arg_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStraightLineEmbedding.lean)
-/
@[path]
private lemma dartAngle_sub_eq_arg_div_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {dart next : G.Dart} :
-- imply
  embedding.dartAngle next - embedding.dartAngle dart = (Complex.arg ((embedding.vertex next.snd - embedding.vertex next.fst) / (embedding.vertex dart.snd - embedding.vertex dart.fst)) : ℝ) := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.dartAngle_sub_eq_arg_div embedding dart next

/--
[KWStraightLineEmbedding.principalPhase_eq_turnPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStraightLineEmbedding.lean)
-/
@[path]
private lemma principalPhase_eq_turnPhase_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {dart next : G.Dart} :
-- imply
  kwPrincipalHalfAnglePhase embedding.dartAngle dart next = embedding.turnPhase dart next := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.principalPhase_eq_turnPhase embedding dart next

/--
[KWStraightLineEmbedding.dartAngle_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStraightLineEmbedding.lean)
-/
@[path]
private lemma dartAngle_symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {dart : G.Dart} :
-- imply
  embedding.dartAngle dart.symm = embedding.dartAngle dart + (Real.pi : Real.Angle) := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.dartAngle_symm embedding dart

/--
[KWStraightLineEmbedding.nonantipodal_of_nonbacktracking](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStraightLineEmbedding.lean)
-/
@[path]
private lemma nonantipodal_of_nonbacktracking_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {dart next : G.Dart}
-- given
  (hadj : G.DartAdj dart next)
  (hneq : dart.edge ≠ next.edge) :
-- imply
  embedding.dartAngle next - embedding.dartAngle dart ≠ (Real.pi : Real.Angle) := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.nonantipodal_of_nonbacktracking embedding dart next hadj hneq

/--
[kwStraightLineGraphLoopWeight_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStraightLineEmbedding.lean)
-/
@[path]
private lemma kwStraightLineGraphLoopWeight_surgery_sign_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {n : ℕ}
  [NeZero n]
  {weight : Sym2 V → ℂ}
  {selected : G.Dart}
  {loop : Fin n → G.Dart}
-- given
  (hboth : (∃ i, loop i = selected) ∧ ∃ j, loop j = selected.symm) :
-- imply
  StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight (kwPrincipalHalfAnglePhase embedding.dartAngle)) (StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop) = -StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight (kwPrincipalHalfAnglePhase embedding.dartAngle)) loop := by
-- proof
  apply StatMech.FrontierA.kwStraightLineGraphLoopWeight_surgery_sign G embedding weight selected loop hboth

/--
[kwStraightLineGraphLoopWeight_turnPhase_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStraightLineEmbedding.lean)
-/
@[path]
private lemma kwStraightLineGraphLoopWeight_turnPhase_surgery_sign_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {n : ℕ}
  [NeZero n]
  {weight : Sym2 V → ℂ}
  {selected : G.Dart}
  {loop : Fin n → G.Dart}
-- given
  (hboth : (∃ i, loop i = selected) ∧ ∃ j, loop j = selected.symm) :
-- imply
  StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight embedding.turnPhase) (StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop) = -StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight embedding.turnPhase) loop := by
-- proof
  apply StatMech.FrontierA.kwStraightLineGraphLoopWeight_turnPhase_surgery_sign G embedding weight selected loop hboth

/--
[kwStraightLineGraphLoopWeight_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStraightLineEmbedding.lean)
-/
@[path]
private lemma kwStraightLineGraphLoopWeight_loopRev_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {n : ℕ}
  [NeZero n]
  {weight : Sym2 V → ℂ}
  {loop : Fin n → G.Dart} :
-- imply
  StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight embedding.turnPhase) (StatMech.Onsager.ons_involutiveLoopRev SimpleGraph.Dart.symm loop) = StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight embedding.turnPhase) loop := by
-- proof
  apply StatMech.FrontierA.kwStraightLineGraphLoopWeight_loopRev G embedding weight loop

/--
[kw_straightLineGraph_fixedOrbitExponent_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStraightLineEmbedding.lean)
-/
@[path]
private lemma kw_straightLineGraph_fixedOrbitExponent_cancel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {n : ℕ}
  [NeZero n]
  {weight : Sym2 V → ℂ}
  {selected : G.Dart}
  {exponent : Sym2 G.Dart →₀ ℕ} :
-- imply
  (∑ loop ∈ kwFixedOrbitExponentLoops (n := n) selected SimpleGraph.Dart.symm exponent, StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight (kwPrincipalHalfAnglePhase embedding.dartAngle)) loop) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_straightLineGraph_fixedOrbitExponent_cancel G embedding weight selected exponent

/--
[kw_straightLineGraph_turnPhase_fixedOrbitExponent_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStraightLineEmbedding.lean)
-/
@[path]
private lemma kw_straightLineGraph_turnPhase_fixedOrbitExponent_cancel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {n : ℕ}
  [NeZero n]
  {weight : Sym2 V → ℂ}
  {selected : G.Dart}
  {exponent : Sym2 G.Dart →₀ ℕ} :
-- imply
  (∑ loop ∈ kwFixedOrbitExponentLoops (n := n) selected SimpleGraph.Dart.symm exponent, StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight embedding.turnPhase) loop) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_straightLineGraph_turnPhase_fixedOrbitExponent_cancel G embedding weight selected exponent


-- created on 2026-10-23
