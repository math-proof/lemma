import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
open StatMech StatMech.FrontierD


/--
[fkMedialCheckerColor_localMate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialCheckerboard.lean)
-/
@[path]
private lemma fkMedialCheckerColor_localMate_ne_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T} :
-- imply
  fkMedialCheckerColor (fkMedialLocalMate pairing d) ≠ fkMedialCheckerColor d := by
-- proof
  apply StatMech.FrontierD.fkMedialCheckerColor_localMate_ne pairing d

/--
[fkMedialCheckerColor_bondMate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialCheckerboard.lean)
-/
@[path]
private lemma fkMedialCheckerColor_bondMate_ne_eq
  {T : EvenTorus}
  {T : EvenTorus}
  {d : FKMedialDart T} :
-- imply
  fkMedialCheckerColor (fkMedialBondMate T d) ≠ fkMedialCheckerColor d := by
-- proof
  apply StatMech.FrontierD.fkMedialCheckerColor_bondMate_ne T d

/--
[fkMedialVertexParity_cyclicPred_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialCheckerboard.lean)
-/
@[path]
private lemma fkMedialVertexParity_cyclicPred_fst_eq
  {T : EvenTorus}
  {T : EvenTorus}
  {i : Fin T.width}
  {j : Fin T.height} :
-- imply
  fkMedialVertexParity (SixVertexArrows.cyclicPred T.width_pos i, j) = !fkMedialVertexParity (i, j) := by
-- proof
  apply StatMech.FrontierD.fkMedialVertexParity_cyclicPred_fst T i j

/--
[fkMedialVertexParity_succ_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialCheckerboard.lean)
-/
@[path]
private lemma fkMedialVertexParity_succ_fst_eq
  {T : EvenTorus}
  {T : EvenTorus}
  {i : Fin T.width}
  {j : Fin T.height} :
-- imply
  fkMedialVertexParity (finitePeriodicSucc T.width_pos i, j) = !fkMedialVertexParity (i, j) := by
-- proof
  apply StatMech.FrontierD.fkMedialVertexParity_succ_fst T i j

/--
[fkMedialVertexParity_cyclicPred_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialCheckerboard.lean)
-/
@[path]
private lemma fkMedialVertexParity_cyclicPred_snd_eq
  {T : EvenTorus}
  {T : EvenTorus}
  {i : Fin T.width}
  {j : Fin T.height} :
-- imply
  fkMedialVertexParity (i, SixVertexArrows.cyclicPred T.height_pos j) = !fkMedialVertexParity (i, j) := by
-- proof
  apply StatMech.FrontierD.fkMedialVertexParity_cyclicPred_snd T i j

/--
[fkMedialVertexParity_succ_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialCheckerboard.lean)
-/
@[path]
private lemma fkMedialVertexParity_succ_snd_eq
  {T : EvenTorus}
  {T : EvenTorus}
  {i : Fin T.width}
  {j : Fin T.height} :
-- imply
  fkMedialVertexParity (i, finitePeriodicSucc T.height_pos j) = !fkMedialVertexParity (i, j) := by
-- proof
  apply StatMech.FrontierD.fkMedialVertexParity_succ_snd T i j

/--
[fkMedialLoopGraph_adj_checkerColor_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialCheckerboard.lean)
-/
@[path]
private lemma fkMedialLoopGraph_adj_checkerColor_ne_eq
  {T : EvenTorus}
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d e : FKMedialDart T}
-- given
  (hde : (fkMedialLoopGraph T pairing).Adj d e) :
-- imply
  fkMedialCheckerColor d ≠ fkMedialCheckerColor e := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopGraph_adj_checkerColor_ne T pairing hde


-- created on 2026-10-23
