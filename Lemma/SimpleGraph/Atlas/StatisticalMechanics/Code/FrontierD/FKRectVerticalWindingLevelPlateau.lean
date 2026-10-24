import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingLevelPlateau
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectMedialBoundaryPrimalSeamTrace_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingLevelPlateau.lean)
-/
@[path]
private lemma fkRectMedialBoundaryPrimalSeamTrace_add_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialDart R.medialTorus}
  {m n : Nat} :
-- imply
  fkRectMedialBoundaryPrimalSeamTrace R pairing d (m + n) = fkRectMedialBoundaryPrimalSeamTrace R pairing d m + fkRectMedialBoundaryPrimalSeamTrace R pairing ((fkMedialBoundaryStep pairing)^[m] d) n := by
-- proof
  apply StatMech.FrontierD.fkRectMedialBoundaryPrimalSeamTrace_add R pairing d m n

/--
[fkRectMedialBoundaryPrimalSeamTrace_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingLevelPlateau.lean)
-/
@[path]
private lemma fkRectMedialBoundaryPrimalSeamTrace_succ_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialDart R.medialTorus}
  {m : Nat} :
-- imply
  fkRectMedialBoundaryPrimalSeamTrace R pairing d (m + 1) = fkRectMedialBoundaryPrimalSeamTrace R pairing d m + fkRectMedialBoundaryPrimalSeamIncrement R pairing ((fkMedialBoundaryStep pairing)^[m] d) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialBoundaryPrimalSeamTrace_succ R pairing d m

/--
[fkRectVerticalSeamIncrement_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingLevelPlateau.lean)
-/
@[path]
private lemma fkRectVerticalSeamIncrement_bounds_eq
  {R : FKRectTorus}
  {x y : R.Vertex} :
-- imply
  -1 ≤ fkRectVerticalSeamIncrement R x y ∧ fkRectVerticalSeamIncrement R x y ≤ 1 := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalSeamIncrement_bounds R x y

/--
[fkRectBlackBoundaryPrefixVerticalLevel_unitSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingLevelPlateau.lean)
-/
@[path]
private lemma fkRectBlackBoundaryPrefixVerticalLevel_unitSteps_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R omega IntUnitSteps (fun m => (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryPrefixVerticalLevel_unitSteps R omega d

/--
[fkRectBlackBoundaryPrimalSeamTrace_two_mul_length_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingLevelPlateau.lean)
-/
@[path]
private lemma fkRectBlackBoundaryPrimalSeamTrace_two_mul_length_snd_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R omega let n := (fkRectBlackOrbitList pairing d).length (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 (2 * n)).2 = 2 * (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryPrimalSeamTrace_two_mul_length_snd R omega d

/--
[exists_fkRectBlackBoundaryUnitPlateauEndpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingLevelPlateau.lean)
-/
@[path]
private lemma exists_fkRectBlackBoundaryUnitPlateauEndpoints_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {j : Fin (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat}
-- given
  (hpos : 0 < (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R omega let n := (fkRectBlackOrbitList pairing d).length let r : Int := j.val + 1 ∃ ab : Nat × Nat, 0 < ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 < 2 * n ∧ (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 (ab.1 - 1)).2 = r - 1 ∧ (∀ m, ab.1 ≤ m → m ≤ ab.2 → (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 = r) ∧ (∀ m < ab.2 + 1, (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 < r + 1) ∧ (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 (ab.2 + 1)).2 = r + 1 := by
-- proof
  apply StatMech.FrontierD.exists_fkRectBlackBoundaryUnitPlateauEndpoints R omega d hpos j

/--
[fkRectBlackBoundaryUnitPlateauEndpoints_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingLevelPlateau.lean)
-/
@[path]
private lemma fkRectBlackBoundaryUnitPlateauEndpoints_spec_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {j : Fin (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat}
-- given
  (hpos : 0 < (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R omega let n := (fkRectBlackOrbitList pairing d).length let ab := fkRectBlackBoundaryUnitPlateauEndpoints R omega d hpos j let r : Int := j.val + 1 0 < ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 < 2 * n ∧ (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 (ab.1 - 1)).2 = r - 1 ∧ (∀ m, ab.1 ≤ m → m ≤ ab.2 → (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 = r) ∧ (∀ m < ab.2 + 1, (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 < r + 1) ∧ (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 (ab.2 + 1)).2 = r + 1 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryUnitPlateauEndpoints_spec R omega d hpos j

/--
[fkRectMedialBoundaryPrimalStep_cutReachable_of_snd_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingLevelPlateau.lean)
-/
@[path]
private lemma fkRectMedialBoundaryPrimalStep_cutReachable_of_snd_eq_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {e : FKMedialDart R.medialTorus}
-- given
  (hzero : (fkRectMedialBoundaryPrimalSeamIncrement R (fkRectConfigurationToMedialPairing R omega) e).2 = 0) :
-- imply
  (fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).Reachable (fkRectMedialDartPrimalLabel R e) (fkRectMedialDartPrimalLabel R (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega) e)) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialBoundaryPrimalStep_cutReachable_of_snd_eq_zero R omega e hzero

/--
[fkRectBlackBoundaryPlateau_cutReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingLevelPlateau.lean)
-/
@[path]
private lemma fkRectBlackBoundaryPlateau_cutReachable_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {a b : Nat}
-- given
  (hab : a ≤ b)
  (hconst : ∀ m, a ≤ m → m ≤ b → (fkRectMedialBoundaryPrimalSeamTrace R (fkRectConfigurationToMedialPairing R omega) d.1 m).2 = (fkRectMedialBoundaryPrimalSeamTrace R (fkRectConfigurationToMedialPairing R omega) d.1 a).2) :
-- imply
  (fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).Reachable (fkRectMedialDartPrimalLabel R ((fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega))^[a] d.1)) (fkRectMedialDartPrimalLabel R ((fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega))^[b] d.1)) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryPlateau_cutReachable R omega d hab hconst

/--
[fkRectVerticalSeamIncrement_eq_one_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingLevelPlateau.lean)
-/
@[path]
private lemma fkRectVerticalSeamIncrement_eq_one_endpoints_eq
  {R : FKRectTorus}
  {x y : R.Vertex}
-- given
  (hinc : fkRectVerticalSeamIncrement R x y = 1) :
-- imply
  x.2 = fkRectTopRow R ∧ y.2 = fkRectBottomRow R := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalSeamIncrement_eq_one_endpoints R x y hinc

/--
[fkRectBlackBoundaryUnitCutComponent_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingLevelPlateau.lean)
-/
@[path]
private lemma fkRectBlackBoundaryUnitCutComponent_crossing_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {j : Fin (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat}
-- given
  (hpos : 0 < (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2) :
-- imply
  FKRectHorizontalCutPrimalCrossingComponent R (fkRectForceHorizontalCutClosed R omega) (fkRectBlackBoundaryUnitCutComponent R omega d hpos j) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryUnitCutComponent_crossing R omega d hpos j


-- created on 2026-10-23
