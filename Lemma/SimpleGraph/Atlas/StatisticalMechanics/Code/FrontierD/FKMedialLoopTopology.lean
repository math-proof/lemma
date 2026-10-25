import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
open SimpleGraph StatMech StatMech.FrontierD


/--
[finitePeriodicSucc_cyclicPred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean)
-/
@[path]
private lemma finitePeriodicSucc_cyclicPred_eq
  {N : Nat}
  {i : Fin N}
-- given
  (hN : 0 < N) :
-- imply
  finitePeriodicSucc hN (SixVertexArrows.cyclicPred hN i) = i := by
-- proof
  apply StatMech.FrontierD.finitePeriodicSucc_cyclicPred hN i

/--
[fkMedialLocalMate_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean)
-/
@[path]
private lemma fkMedialLocalMate_involutive_eq
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T} :
-- imply
  fkMedialLocalMate pairing (fkMedialLocalMate pairing d) = d := by
-- proof
  apply StatMech.FrontierD.fkMedialLocalMate_involutive pairing d

/--
[fkMedialBondMate_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean)
-/
@[path]
private lemma fkMedialBondMate_involutive_eq
  {T : EvenTorus}
  {d : FKMedialDart T} :
-- imply
  fkMedialBondMate T (fkMedialBondMate T d) = d := by
-- proof
  apply StatMech.FrontierD.fkMedialBondMate_involutive T d

/--
[fkMedialLocalMate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean)
-/
@[path]
private lemma fkMedialLocalMate_ne_eq
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T} :
-- imply
  fkMedialLocalMate pairing d ≠ d := by
-- proof
  apply StatMech.FrontierD.fkMedialLocalMate_ne pairing d

/--
[fkMedialBondMate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean)
-/
@[path]
private lemma fkMedialBondMate_ne_eq
  {T : EvenTorus}
  {d : FKMedialDart T} :
-- imply
  fkMedialBondMate T d ≠ d := by
-- proof
  apply StatMech.FrontierD.fkMedialBondMate_ne T d

/--
[fkMedialLoopGraph_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean)
-/
@[path]
private lemma fkMedialLoopGraph_adj_iff_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d e : FKMedialDart T} :
-- imply
  (fkMedialLoopGraph T pairing).Adj d e ↔ e = fkMedialLocalMate pairing d ∨ e = fkMedialBondMate T d := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopGraph_adj_iff T pairing d e

/--
[fkMedialLocalMate_ne_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean)
-/
@[path]
private lemma fkMedialLocalMate_ne_bondMate_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T} :
-- imply
  fkMedialLocalMate pairing d ≠ fkMedialBondMate T d := by
-- proof
  apply StatMech.FrontierD.fkMedialLocalMate_ne_bondMate T pairing d

/--
[fkMedialLoopGraph_neighborFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean)
-/
@[path]
private lemma fkMedialLoopGraph_neighborFinset_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T} :
-- imply
  (fkMedialLoopGraph T pairing).neighborFinset d = {fkMedialLocalMate pairing d, fkMedialBondMate T d} := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopGraph_neighborFinset T pairing d

/--
[fkMedialLoopGraph_degree_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean)
-/
@[path]
private lemma fkMedialLoopGraph_degree_eq_two_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T} :
-- imply
  (fkMedialLoopGraph T pairing).degree d = 2 := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopGraph_degree_eq_two T pairing d

/--
[fkMedialDartIncoming_localMate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean)
-/
@[path]
private lemma fkMedialDartIncoming_localMate_ne_eq
  {pairing : FKMedialLoopPairing T}
  {omega : SixVertexArrows T}
  {d : FKMedialDart T}
-- given
  (hcompat : forall v, fkLoopPairingCompatible (pairing v) omega v) :
-- imply
  fkMedialDartIncoming omega (fkMedialLocalMate pairing d) ≠ fkMedialDartIncoming omega d := by
-- proof
  apply StatMech.FrontierD.fkMedialDartIncoming_localMate_ne pairing omega hcompat d

/--
[fkMedialDartIncoming_bondMate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean)
-/
@[path]
private lemma fkMedialDartIncoming_bondMate_ne_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {d : FKMedialDart T} :
-- imply
  fkMedialDartIncoming omega (fkMedialBondMate T d) ≠ fkMedialDartIncoming omega d := by
-- proof
  apply StatMech.FrontierD.fkMedialDartIncoming_bondMate_ne T omega d

/--
[fkMedialLoopGraph_adj_incoming_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean)
-/
@[path]
private lemma fkMedialLoopGraph_adj_incoming_ne_eq
  {pairing : FKMedialLoopPairing T}
  {omega : SixVertexArrows T}
  {d e : FKMedialDart T}
-- given
  (hcompat : forall v, fkLoopPairingCompatible (pairing v) omega v)
  (hde : (fkMedialLoopGraph T pairing).Adj d e) :
-- imply
  fkMedialDartIncoming omega d ≠ fkMedialDartIncoming omega e := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopGraph_adj_incoming_ne pairing omega hcompat hde

/--
[sum_bool_toNat_eq_sixVertexUpCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean)
-/
@[path]
private lemma sum_bool_toNat_eq_sixVertexUpCount_eq
  {N : Nat}
  {x : SixVertexRow N} :
-- imply
  (∑ i, (x i).toNat) = sixVertexUpCount x := by
-- proof
  apply StatMech.FrontierD.sum_bool_toNat_eq_sixVertexUpCount x

/--
[fkOrientedLoopVerticalFlux_eq_charge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean)
-/
@[path]
private lemma fkOrientedLoopVerticalFlux_eq_charge_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T} :
-- imply
  fkOrientedLoopVerticalFlux T omega = 2 * (sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) : Int) - (T.width : Int) := by
-- proof
  apply StatMech.FrontierD.fkOrientedLoopVerticalFlux_eq_charge T omega

/--
[fkOrientedLoopVerticalFlux_eq_neg_two_mul_of_fixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean)
-/
@[path]
private lemma fkOrientedLoopVerticalFlux_eq_neg_two_mul_of_fixedCharge_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {r : Nat}
-- given
  (hr : r <= T.width / 2)
  (hsector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = T.width / 2 - r) :
-- imply
  fkOrientedLoopVerticalFlux T omega = -(2 * (r : Int)) := by
-- proof
  apply StatMech.FrontierD.fkOrientedLoopVerticalFlux_eq_neg_two_mul_of_fixedCharge T omega r hr hsector


-- created on 2026-10-23
