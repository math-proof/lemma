import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry
open StatMech StatMech.FrontierD


/--
[fkRectBlackBoundary_strandStep_eq_medialStep_add_potential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackBoundary_strandStep_eq_medialStep_add_potential_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  let a := stepOf (fkRectBlackBoundaryMedialDirection pairing d) let p := fkRectMedialSidePotential d.1.2 let q := fkRectMedialSidePotential ((fkMedialBlackBoundaryPerm pairing d).1.2) stepOf (fkMedialStrandDirection pairing d.1) = (a.1 + a.2 + q.1 - p.1, a.1 - a.2 + q.2 - p.2) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundary_strandStep_eq_medialStep_add_potential pairing d

/--
[fkRectBlackOrbitList_get_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitList_get_add_one_eq
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T}
  [NeZero (fkRectBlackOrbitList pairing d).length]
  {i : Fin (fkRectBlackOrbitList pairing d).length} :
-- imply
  (fkRectBlackOrbitList pairing d).get (i + 1) = fkMedialBlackBoundaryPerm pairing ((fkRectBlackOrbitList pairing d).get i) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitList_get_add_one pairing d i

/--
[fkRectBlackOrbitDisplacement_eq_diagonal_medialDisplacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitDisplacement_eq_diagonal_medialDisplacement_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R omega let medial := ons_pathDisplacement (List.ofFn fun i => fkRectBlackBoundaryMedialDirection pairing ((fkRectBlackOrbitList pairing d).get i)) ons_pathDisplacement (List.ofFn (fkRectBlackOrbitDirection pairing d)) = (medial.1 + medial.2, medial.1 - medial.2) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitDisplacement_eq_diagonal_medialDisplacement R omega d

/--
[fkRectBlackOrbitDisplacement_eq_two_deck_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitDisplacement_eq_two_deck_winding_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  ons_pathDisplacement (List.ofFn (fkRectBlackOrbitDirection (fkRectConfigurationToMedialPairing R omega) d)) = 2 • fkRectSquareDeckTranslation R (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitDisplacement_eq_two_deck_winding R omega d

/--
[fkRectBlackOrbitMedialDisplacement_eq_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitMedialDisplacement_eq_winding_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R omega let w := fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d) ons_pathDisplacement (List.ofFn fun i => fkRectBlackBoundaryMedialDirection pairing ((fkRectBlackOrbitList pairing d).get i)) = (((2 * R.width : ℕ) : ℤ) * w.1, (R.height : ℤ) * w.2) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitMedialDisplacement_eq_winding R omega d

/--
[fkRectMedialRibbonBlock_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectMedialRibbonBlock_length_eq
  {pairing : Bool}
  {side : FKMedialSide} :
-- imply
  (fkRectMedialRibbonBlock pairing side).length = 8 := by
-- proof
  apply StatMech.FrontierD.fkRectMedialRibbonBlock_length pairing side

/--
[fkRectMedialRibbonBlock_step_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectMedialRibbonBlock_step_sum_eq
  {pairing : Bool}
  {side : FKMedialSide} :
-- imply
  let medialDir := fkRectMedialSideDirection (fkRectMedialLocalMateSide pairing side) let nextSide := fkRectMedialOppositeSide (fkRectMedialLocalMateSide pairing side) ((fkRectMedialRibbonBlock pairing side).map stepOf).sum = (8 * (stepOf medialDir).1 + (fkRectMedialRibbonPortOffset nextSide).1 - (fkRectMedialRibbonPortOffset side).1, 8 * (stepOf medialDir).2 + (fkRectMedialRibbonPortOffset nextSide).2 - (fkRectMedialRibbonPortOffset side).2) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialRibbonBlock_step_sum pairing side

/--
[fkRectMedialOppositeSide_localMate_eq_boundaryPerm_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectMedialOppositeSide_localMate_eq_boundaryPerm_side_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  fkRectMedialOppositeSide (fkMedialLocalMate pairing d.1).2 = (fkMedialBlackBoundaryPerm pairing d).1.2 := by
-- proof
  apply StatMech.FrontierD.fkRectMedialOppositeSide_localMate_eq_boundaryPerm_side pairing d

/--
[fkRectBlackOrbitMedialRibbonWord_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitMedialRibbonWord_length_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  (fkRectBlackOrbitMedialRibbonWord R omega d).length = 8 * (fkRectBlackOrbitList (fkRectConfigurationToMedialPairing R omega) d).length := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitMedialRibbonWord_length R omega d

/--
[fkRectBlackOrbitMedialRibbonWord_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitMedialRibbonWord_nonempty_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  fkRectBlackOrbitMedialRibbonWord R omega d ≠ [] := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitMedialRibbonWord_nonempty R omega d

/--
[fkRectBlackOrbitMedialRibbonWord_step_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitMedialRibbonWord_step_sum_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  let w := fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d) ((fkRectBlackOrbitMedialRibbonWord R omega d).map stepOf).sum = (8 * ((2 * R.width : ℕ) : ℤ) * w.1, 8 * (R.height : ℤ) * w.2) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitMedialRibbonWord_step_sum R omega d

/--
[fkRectBlackOrbitRibbonSubdivisionSide_gt_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionSide_gt_two_eq
  {R : FKRectTorus} :
-- imply
  2 < fkRectBlackOrbitRibbonSubdivisionSide R := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionSide_gt_two R

/--
[fkRectBlackOrbitRibbonSubdivisionWord_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionWord_nonempty_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  fkRectBlackOrbitRibbonSubdivisionWord R omega d ≠ [] := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionWord_nonempty R omega d

/--
[fkRectBlackOrbitRibbonSubdivisionWord_preserves_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionWord_preserves_winding_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  let w := fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d) ((fkRectBlackOrbitRibbonSubdivisionWord R omega d).map ons_dirExponentX).sum = (fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.1 ∧ ((fkRectBlackOrbitRibbonSubdivisionWord R omega d).map ons_dirExponentY).sum = (fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.2 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionWord_preserves_winding R omega d

/--
[fkRectBlackOrbitRibbonSubdivisionDart_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionDart_valid_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  ∀ k, (fkRectBlackOrbitRibbonSubdivisionDart R omega d k).1 = ons_dirStep (fkRectBlackOrbitRibbonSubdivisionSide R) (fkRectBlackOrbitRibbonSubdivisionDart R omega d (k + 1)).2 (fkRectBlackOrbitRibbonSubdivisionDart R omega d (k + 1)).1 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionDart_valid R omega d

/--
[fkRectBlackOrbitRibbonSubdivisionDart_exponentX_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionDart_exponentX_sum_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  let w := fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d) (∑ k, ons_dirExponentX (fkRectBlackOrbitRibbonSubdivisionDart R omega d k).2) = (fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.1 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionDart_exponentX_sum R omega d

/--
[fkRectBlackOrbitRibbonSubdivisionDart_exponentY_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionDart_exponentY_sum_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  let w := fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d) (∑ k, ons_dirExponentY (fkRectBlackOrbitRibbonSubdivisionDart R omega d k).2) = (fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.2 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionDart_exponentY_sum R omega d

/--
[fkRectBlackOrbitShearSubdivisionWord_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitShearSubdivisionWord_nonempty_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  fkRectBlackOrbitShearSubdivisionWord R omega d ≠ [] := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitShearSubdivisionWord_nonempty R omega d

/--
[fkRectBlackOrbitShearSubdivisionWord_cyclicNonUturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitShearSubdivisionWord_cyclicNonUturn_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  onsCyclicDirectionNonUturn (fkRectBlackOrbitShearSubdivisionWord R omega d) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitShearSubdivisionWord_cyclicNonUturn R omega d

/--
[fkRectBlackOrbitShearSubdivisionWord_preserves_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitShearSubdivisionWord_preserves_winding_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  let w := fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d) ((fkRectBlackOrbitShearSubdivisionWord R omega d).map ons_dirExponentX).sum = (fkRectBlackOrbitSubdivisionSide R : ℕ) * w.1 ∧ ((fkRectBlackOrbitShearSubdivisionWord R omega d).map ons_dirExponentY).sum = (fkRectBlackOrbitSubdivisionSide R : ℕ) * w.2 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitShearSubdivisionWord_preserves_winding R omega d

/--
[fkRectBlackOrbitSubdivisionSide_gt_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitSubdivisionSide_gt_two_eq
  {R : FKRectTorus} :
-- imply
  2 < fkRectBlackOrbitSubdivisionSide R := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitSubdivisionSide_gt_two R

/--
[fkRectBlackOrbitSubdivisionDart_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitSubdivisionDart_valid_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  ∀ k, (fkRectBlackOrbitSubdivisionDart R omega d k).1 = ons_dirStep (fkRectBlackOrbitSubdivisionSide R) (fkRectBlackOrbitSubdivisionDart R omega d (k + 1)).2 (fkRectBlackOrbitSubdivisionDart R omega d (k + 1)).1 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitSubdivisionDart_valid R omega d

/--
[fkRectBlackOrbitSubdivisionDart_nonUturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitSubdivisionDart_nonUturn_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  ∀ k, (fkRectBlackOrbitSubdivisionDart R omega d k).2 ≠ (fkRectBlackOrbitSubdivisionDart R omega d (k + 1)).2 + 2 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitSubdivisionDart_nonUturn R omega d

/--
[fkRectBlackOrbitSubdivisionDart_exponentX_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitSubdivisionDart_exponentX_sum_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  let w := fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d) (∑ k, ons_dirExponentX (fkRectBlackOrbitSubdivisionDart R omega d k).2) = (fkRectBlackOrbitSubdivisionSide R : ℤ) * w.1 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitSubdivisionDart_exponentX_sum R omega d

/--
[fkRectBlackOrbitSubdivisionDart_exponentY_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitSubdivisionDart_exponentY_sum_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  let w := fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d) (∑ k, ons_dirExponentY (fkRectBlackOrbitSubdivisionDart R omega d k).2) = (fkRectBlackOrbitSubdivisionSide R : ℤ) * w.2 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitSubdivisionDart_exponentY_sum R omega d

/--
[fkRectBlackBoundaryPrimalCycleWinding_fst_odd_of_site_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean)
-/
@[path]
private lemma fkRectBlackBoundaryPrimalCycleWinding_fst_odd_of_site_injective_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
-- given
  (hsite : Function.Injective (fun k ↦ (fkRectBlackOrbitSubdivisionDart R omega d k).1))
  (hy : (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 = 0)
  (hx : (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).1 ≠ 0) :
-- imply
  Odd (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).1 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryPrimalCycleWinding_fst_odd_of_site_injective R omega d hsite hy hx


-- created on 2026-10-23
