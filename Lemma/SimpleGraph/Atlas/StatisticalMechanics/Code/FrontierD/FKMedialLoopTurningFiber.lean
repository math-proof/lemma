import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber
open Equiv Finset SimpleGraph StatMech StatMech.FrontierD StatMech.FrontierD.FKMedialTurningFiber


/--
[local_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean)
-/
@[path]
private lemma local_eq_eq
  {T : EvenTorus}
  {lam : Real}
  {pairing : Bool}
  {a : SixVertexArrows T}
  {v : T.Vertex}
-- given
  (h : fkLoopPairingCompatible pairing a v) :
-- imply
  fkOrientedLoopLocalWeight lam pairing a v = Real.exp ((lam / 4) * vertexTurn pairing a v) := by
-- proof
  apply StatMech.FrontierD.FKMedialTurningFiber.local_eq lam pairing a v h

/--
[modeIncoming_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean)
-/
@[path]
private lemma modeIncoming_bondMate_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {mode : FKMedialLoop T pairing → Bool}
  {d : FKMedialDart T} :
-- imply
  (!modeIncoming pairing mode (fkMedialBondMate T d)) = modeIncoming pairing mode d := by
-- proof
  apply StatMech.FrontierD.FKMedialTurningFiber.modeIncoming_bondMate pairing mode d

/--
[incoming_arrowsOfMode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean)
-/
@[path]
private lemma incoming_arrowsOfMode_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {mode : FKMedialLoop T pairing → Bool}
  {d : FKMedialDart T} :
-- imply
  fkMedialDartIncoming (arrowsOfMode pairing mode) d = modeIncoming pairing mode d := by
-- proof
  apply StatMech.FrontierD.FKMedialTurningFiber.incoming_arrowsOfMode pairing mode d

/--
[compatible_arrowsOfMode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean)
-/
@[path]
private lemma compatible_arrowsOfMode_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {mode : FKMedialLoop T pairing → Bool} :
-- imply
  ∀ v, fkLoopPairingCompatible (pairing v) (arrowsOfMode pairing mode) v := by
-- proof
  apply StatMech.FrontierD.FKMedialTurningFiber.compatible_arrowsOfMode pairing mode

/--
[incoming_eq_color_iff_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean)
-/
@[path]
private lemma incoming_eq_color_iff_reachable_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {a : SixVertexArrows T}
  {d e : FKMedialDart T}
-- given
  (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) a v)
  (hde : (fkMedialLoopGraph T pairing).Reachable d e) :
-- imply
  (fkMedialDartIncoming a d = fkMedialCheckerColor d ↔ fkMedialDartIncoming a e = fkMedialCheckerColor e) := by
-- proof
  apply StatMech.FrontierD.FKMedialTurningFiber.incoming_eq_color_iff_reachable pairing a hcompat hde

/--
[modeIncoming_modeOfArrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean)
-/
@[path]
private lemma modeIncoming_modeOfArrows_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {a : SixVertexArrows T}
  {d : FKMedialDart T}
-- given
  (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) a v) :
-- imply
  modeIncoming pairing (modeOfArrows pairing a) d = fkMedialDartIncoming a d := by
-- proof
  apply StatMech.FrontierD.FKMedialTurningFiber.modeIncoming_modeOfArrows pairing a hcompat d

/--
[arrowsOfMode_modeOfArrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean)
-/
@[path]
private lemma arrowsOfMode_modeOfArrows_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {a : SixVertexArrows T}
-- given
  (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) a v) :
-- imply
  arrowsOfMode pairing (modeOfArrows pairing a) = a := by
-- proof
  apply StatMech.FrontierD.FKMedialTurningFiber.arrowsOfMode_modeOfArrows pairing a hcompat

/--
[modeOfArrows_arrowsOfMode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean)
-/
@[path]
private lemma modeOfArrows_arrowsOfMode_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {mode : FKMedialLoop T pairing → Bool} :
-- imply
  modeOfArrows pairing (arrowsOfMode pairing mode) = mode := by
-- proof
  apply StatMech.FrontierD.FKMedialTurningFiber.modeOfArrows_arrowsOfMode pairing mode

/--
[componentTurn_arrowsOfMode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean)
-/
@[path]
private lemma componentTurn_arrowsOfMode_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {mode : FKMedialLoop T pairing → Bool}
  {C : FKMedialLoop T pairing} :
-- imply
  componentTurn pairing (arrowsOfMode pairing mode) C = if mode C then -canonicalComponentTurn pairing C else canonicalComponentTurn pairing C := by
-- proof
  apply StatMech.FrontierD.FKMedialTurningFiber.componentTurn_arrowsOfMode pairing mode C

/--
[sum_componentTurn_eq_vertexTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean)
-/
@[path]
private lemma sum_componentTurn_eq_vertexTurn_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {a : SixVertexArrows T} :
-- imply
  (∑ C : FKMedialLoop T pairing, componentTurn pairing a C) = ∑ v : T.Vertex, vertexTurn (pairing v) a v := by
-- proof
  apply StatMech.FrontierD.FKMedialTurningFiber.sum_componentTurn_eq_vertexTurn pairing a

/--
[orientedLoopWeight_eq_exp_sum_componentTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean)
-/
@[path]
private lemma orientedLoopWeight_eq_exp_sum_componentTurn_eq
  {T : EvenTorus}
  {lam : Real}
  {pairing : FKMedialLoopPairing T}
  {a : SixVertexArrows T}
-- given
  (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) a v) :
-- imply
  fkOrientedLoopPairingWeight lam pairing a = Real.exp ((lam / 4) * ∑ C : FKMedialLoop T pairing, componentTurn pairing a C) := by
-- proof
  apply StatMech.FrontierD.FKMedialTurningFiber.orientedLoopWeight_eq_exp_sum_componentTurn lam pairing a hcompat

/--
[orientedLoopWeight_arrowsOfMode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean)
-/
@[path]
private lemma orientedLoopWeight_arrowsOfMode_eq
  {T : EvenTorus}
  {lam : Real}
  {pairing : FKMedialLoopPairing T}
  {mode : FKMedialLoop T pairing → Bool} :
-- imply
  fkOrientedLoopPairingWeight lam pairing (arrowsOfMode pairing mode) = ∏ C : FKMedialLoop T pairing, if mode C then Real.exp (-(lam / 4) * canonicalComponentTurn pairing C) else Real.exp ((lam / 4) * canonicalComponentTurn pairing C) := by
-- proof
  apply StatMech.FrontierD.FKMedialTurningFiber.orientedLoopWeight_arrowsOfMode lam pairing mode

/--
[sum_orientedLoopWeight_eq_sum_modes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean)
-/
@[path]
private lemma sum_orientedLoopWeight_eq_sum_modes_eq
  {T : EvenTorus}
  {lam : Real}
  {pairing : FKMedialLoopPairing T} :
-- imply
  (∑ a : SixVertexArrows T, fkOrientedLoopPairingWeight lam pairing a) = ∑ mode : (FKMedialLoop T pairing → Bool), fkOrientedLoopPairingWeight lam pairing (arrowsOfMode pairing mode) := by
-- proof
  apply StatMech.FrontierD.FKMedialTurningFiber.sum_orientedLoopWeight_eq_sum_modes lam pairing

/--
[sum_orientedLoopWeight_eq_turningProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean)
-/
@[path]
private lemma sum_orientedLoopWeight_eq_turningProduct_eq
  {T : EvenTorus}
  {lam : Real}
  {pairing : FKMedialLoopPairing T} :
-- imply
  (∑ a : SixVertexArrows T, fkOrientedLoopPairingWeight lam pairing a) = ∏ C : FKMedialLoop T pairing, (Real.exp ((lam / 4) * canonicalComponentTurn pairing C) + Real.exp (-(lam / 4) * canonicalComponentTurn pairing C)) := by
-- proof
  apply StatMech.FrontierD.FKMedialTurningFiber.sum_orientedLoopWeight_eq_turningProduct lam pairing

/--
[orientationFactor_eq_two_of_turn_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean)
-/
@[path]
private lemma orientationFactor_eq_two_of_turn_eq_zero_eq
  {T : EvenTorus}
  {lam : Real}
  {pairing : FKMedialLoopPairing T}
  {C : FKMedialLoop T pairing}
-- given
  (hC : canonicalComponentTurn pairing C = 0) :
-- imply
  Real.exp ((lam / 4) * canonicalComponentTurn pairing C) + Real.exp (-(lam / 4) * canonicalComponentTurn pairing C) = 2 := by
-- proof
  apply StatMech.FrontierD.FKMedialTurningFiber.orientationFactor_eq_two_of_turn_eq_zero lam pairing C hC

/--
[orientationFactor_eq_exp_add_exp_neg_of_turn_eq_four_or_neg_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean)
-/
@[path]
private lemma orientationFactor_eq_exp_add_exp_neg_of_turn_eq_four_or_neg_four_eq
  {T : EvenTorus}
  {lam : Real}
  {pairing : FKMedialLoopPairing T}
  {C : FKMedialLoop T pairing}
-- given
  (hC : canonicalComponentTurn pairing C = 4 ∨ canonicalComponentTurn pairing C = -4) :
-- imply
  Real.exp ((lam / 4) * canonicalComponentTurn pairing C) + Real.exp (-(lam / 4) * canonicalComponentTurn pairing C) = Real.exp lam + Real.exp (-lam) := by
-- proof
  apply StatMech.FrontierD.FKMedialTurningFiber.orientationFactor_eq_exp_add_exp_neg_of_turn_eq_four_or_neg_four lam pairing C hC


-- created on 2026-10-23
