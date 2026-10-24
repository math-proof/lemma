import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces
open StatMech StatMech.Universality


/--
[fkIsingSquareWedgeFaceKey_open_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean)
-/
@[path]
private lemma fkIsingSquareWedgeFaceKey_open_localMate_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)} :
-- imply
  fkIsingSquareWedgeFaceKey n (FKIsingMedialDart.localMate (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) d) = fkIsingSquareWedgeFaceKey n d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWedgeFaceKey_open_localMate n d

/--
[fkIsingSquareWedgeFaceKey_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean)
-/
@[path]
private lemma fkIsingSquareWedgeFaceKey_bondMate_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hdint : fkIsingSquareInteriorFaceKey n (fkIsingSquareWedgeFaceKey n d)) :
-- imply
  fkIsingSquareWedgeFaceKey n (fkIsingSquareBondMate n hn d) = fkIsingSquareWedgeFaceKey n d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWedgeFaceKey_bondMate n hn d hdint

/--
[fkIsingSquareWiredBoundaryDart_faceKey_not_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean)
-/
@[path]
private lemma fkIsingSquareWiredBoundaryDart_faceKey_not_interior_eq
  {n : Nat}
  {i : FKIsingSquareWiredBoundaryDartIndex n}
-- given
  (hn : 0 < n) :
-- imply
  ¬ fkIsingSquareInteriorFaceKey n (fkIsingSquareWedgeFaceKey n (fkIsingSquareWiredBoundaryDart n hn i)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBoundaryDart_faceKey_not_interior n hn i

/--
[fkIsingSquareWiredBondMate_eq_bondMate_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean)
-/
@[path]
private lemma fkIsingSquareWiredBondMate_eq_bondMate_of_interior_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hd : fkIsingSquareInteriorFaceKey n (fkIsingSquareWedgeFaceKey n d)) :
-- imply
  fkIsingSquareWiredBondMate n hn d = fkIsingSquareBondMate n hn d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d hd

/--
[fkIsingSquareInteriorCellVertex_east_available](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean)
-/
@[path]
private lemma fkIsingSquareInteriorCellVertex_east_available_eq
  {n : Nat}
  {c : FKIsingSquareInteriorCell n} :
-- imply
  fkIsingSquareDirectionAvailable n (fkIsingSquareInteriorCellVertex n c) .east := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorCellVertex_east_available n c

/--
[fkIsingSquareInteriorCellBlack_faceKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean)
-/
@[path]
private lemma fkIsingSquareInteriorCellBlack_faceKey_eq
  {n : Nat}
  {c : FKIsingSquareInteriorCell n} :
-- imply
  fkIsingSquareWiredBlackFaceKey n (fkIsingSquareInteriorCellBlack n c) = some (fkIsingSquareInteriorCellKey n c) := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorCellBlack_faceKey n c

/--
[fkIsingSquareInteriorCellKey_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean)
-/
@[path]
private lemma fkIsingSquareInteriorCellKey_interior_eq
  {n : Nat}
  {c : FKIsingSquareInteriorCell n} :
-- imply
  fkIsingSquareInteriorFaceKey n (fkIsingSquareInteriorCellKey n c) := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorCellKey_interior n c

/--
[fkIsingSquareInteriorCellKey_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean)
-/
@[path]
private lemma fkIsingSquareInteriorCellKey_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (fkIsingSquareInteriorCellKey n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorCellKey_injective n

/--
[fkIsingSquareWiredFullInteriorCycle_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean)
-/
@[path]
private lemma fkIsingSquareWiredFullInteriorCycle_injective_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  Function.Injective (fkIsingSquareWiredFullInteriorCycle n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredFullInteriorCycle_injective n hn

/--
[fkIsingSquareWiredFullLeftCycle_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean)
-/
@[path]
private lemma fkIsingSquareWiredFullLeftCycle_injective_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  Function.Injective (fkIsingSquareWiredFullLeftCycle n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredFullLeftCycle_injective n hn

/--
[fkIsingSquareWiredFullCycle_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean)
-/
@[path]
private lemma fkIsingSquareWiredFullCycle_injective_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  Function.Injective (fkIsingSquareWiredFullCycle n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredFullCycle_injective n hn

/--
[fkIsingSquareWired_full_completed_componentCount_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean)
-/
@[path]
private lemma fkIsingSquareWired_full_completed_componentCount_lower_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  (2 * n + 1) ^ 2 - 2 * n ≤ Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)).ConnectedComponent := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_full_completed_componentCount_lower n hn

/--
[fkIsingSquareWired_full_completed_componentCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean)
-/
@[path]
private lemma fkIsingSquareWired_full_completed_componentCount_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)).ConnectedComponent = (2 * n + 1) ^ 2 - 2 * n := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_full_completed_componentCount n hn

/--
[fkIsingSquareWiredEulerDefect_empty_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean)
-/
@[path]
private lemma fkIsingSquareWiredEulerDefect_empty_full_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) = fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig ∅) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredEulerDefect_empty_full n hn

/--
[fkIsingSquareWiredEulerDefect_toggle_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean)
-/
@[path]
private lemma fkIsingSquareWiredEulerDefect_toggle_eq_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredEulerDefect n hn (setOpen e.1 omega) = fkIsingSquareWiredEulerDefect n hn (setClosed e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredEulerDefect_toggle_eq n hn omega e


-- created on 2026-10-23
