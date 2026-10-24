import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation
open SimpleGraph Equiv StatMech StatMech.FrontierD


/--
[fkMedialBoundaryStep_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryPermutation.lean)
-/
@[path]
private lemma fkMedialBoundaryStep_apply_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T} :
-- imply
  fkMedialBoundaryStep pairing d = fkMedialBondMate T (fkMedialLocalMate pairing d) := by
-- proof
  apply StatMech.FrontierD.fkMedialBoundaryStep_apply pairing d

/--
[fkMedialCheckerColor_boundaryStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryPermutation.lean)
-/
@[path]
private lemma fkMedialCheckerColor_boundaryStep_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T} :
-- imply
  fkMedialCheckerColor (fkMedialBoundaryStep pairing d) = fkMedialCheckerColor d := by
-- proof
  apply StatMech.FrontierD.fkMedialCheckerColor_boundaryStep pairing d

/--
[fkMedialBlackBoundaryPerm_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryPermutation.lean)
-/
@[path]
private lemma fkMedialBlackBoundaryPerm_val_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  (fkMedialBlackBoundaryPerm pairing d).1 = fkMedialBondMate T (fkMedialLocalMate pairing d.1) := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackBoundaryPerm_val pairing d

/--
[fkMedialBlackBoundaryPerm_val_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryPermutation.lean)
-/
@[path]
private lemma fkMedialBlackBoundaryPerm_val_step_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  (fkMedialBlackBoundaryPerm pairing d).1 = fkMedialBoundaryStep pairing d.1 := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackBoundaryPerm_val_step pairing d

/--
[fkMedialBoundaryStep_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryPermutation.lean)
-/
@[path]
private lemma fkMedialBoundaryStep_reachable_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T} :
-- imply
  (fkMedialLoopGraph T pairing).Reachable d (fkMedialBoundaryStep pairing d) := by
-- proof
  apply StatMech.FrontierD.fkMedialBoundaryStep_reachable pairing d

/--
[fkMedialBoundaryStep_iterate_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryPermutation.lean)
-/
@[path]
private lemma fkMedialBoundaryStep_iterate_reachable_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T}
  {n : Nat} :
-- imply
  (fkMedialLoopGraph T pairing).Reachable d ((fkMedialBoundaryStep pairing)^[n] d) := by
-- proof
  apply StatMech.FrontierD.fkMedialBoundaryStep_iterate_reachable pairing d n

/--
[fkMedialBoundaryStep_iterate_ne_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryPermutation.lean)
-/
@[path]
private lemma fkMedialBoundaryStep_iterate_ne_of_not_reachable_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d e : FKMedialDart T}
  {n : Nat}
-- given
  (hde : ¬ (fkMedialLoopGraph T pairing).Reachable d e) :
-- imply
  (fkMedialBoundaryStep pairing)^[n] d ≠ e := by
-- proof
  apply StatMech.FrontierD.fkMedialBoundaryStep_iterate_ne_of_not_reachable pairing hde n

/--
[fkMedial_reachable_of_blackBoundary_sameCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryPermutation.lean)
-/
@[path]
private lemma fkMedial_reachable_of_blackBoundary_sameCycle_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d e : FKMedialBlackDart T}
-- given
  (hde : (fkMedialBlackBoundaryPerm pairing).SameCycle d e) :
-- imply
  (fkMedialLoopGraph T pairing).Reachable d.1 e.1 := by
-- proof
  apply StatMech.FrontierD.fkMedial_reachable_of_blackBoundary_sameCycle pairing d e hde

/--
[fkMedial_blackBoundary_sameCycle_of_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryPermutation.lean)
-/
@[path]
private lemma fkMedial_blackBoundary_sameCycle_of_walk_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d e : FKMedialDart T}
  {p : (fkMedialLoopGraph T pairing).Walk d e}
-- given
  (hd : fkMedialCheckerColor d = false)
  (he : fkMedialCheckerColor e = false) :
-- imply
  (fkMedialBlackBoundaryPerm pairing).SameCycle ⟨d, hd⟩ ⟨e, he⟩ := by
-- proof
  apply StatMech.FrontierD.fkMedial_blackBoundary_sameCycle_of_walk pairing p hd he

/--
[fkMedial_blackBoundary_sameCycle_iff_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryPermutation.lean)
-/
@[path]
private lemma fkMedial_blackBoundary_sameCycle_iff_reachable_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d e : FKMedialBlackDart T} :
-- imply
  (fkMedialBlackBoundaryPerm pairing).SameCycle d e ↔ (fkMedialLoopGraph T pairing).Reachable d.1 e.1 := by
-- proof
  apply StatMech.FrontierD.fkMedial_blackBoundary_sameCycle_iff_reachable pairing d e

/--
[fkMedialBlackBoundaryCycleToLoop_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryPermutation.lean)
-/
@[path]
private lemma fkMedialBlackBoundaryCycleToLoop_bijective_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T} :
-- imply
  Function.Bijective (fkMedialBlackBoundaryCycleToLoop pairing) := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackBoundaryCycleToLoop_bijective pairing

/--
[permCycleCount_fkMedialBlackBoundaryPerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryPermutation.lean)
-/
@[path]
private lemma permCycleCount_fkMedialBlackBoundaryPerm_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T} :
-- imply
  StatMech.FrontierA.permCycleCount (fkMedialBlackBoundaryPerm pairing) = fkMedialLoopCount T pairing := by
-- proof
  apply StatMech.FrontierD.permCycleCount_fkMedialBlackBoundaryPerm pairing


-- created on 2026-10-23
