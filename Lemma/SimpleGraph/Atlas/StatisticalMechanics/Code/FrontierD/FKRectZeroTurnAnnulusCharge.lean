import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge
open StatMech StatMech.FrontierD


/--
[mem_fkRectRawPrimalCrossingLeftRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma mem_fkRectRawPrimalCrossingLeftRows_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {y : Fin R.height} :
-- imply
  y ∈ fkRectRawPrimalCrossingLeftRows R omega C ↔ (fkRectOpenGraph R (fkRectForceCutClosed R omega)).connectedComponentMk (fkRectLeftColumn R, y) = C.1 := by
-- proof
  apply StatMech.FrontierD.mem_fkRectRawPrimalCrossingLeftRows R omega C y

/--
[fkRectRawPrimalCrossingLeftRows_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingLeftRows_nonempty_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectRawPrimalHorizontalCrossingComponent R omega} :
-- imply
  (fkRectRawPrimalCrossingLeftRows R omega C).Nonempty := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingLeftRows_nonempty R omega C

/--
[fkRectRawPrimalCrossingFirstRow_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingFirstRow_component_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectRawPrimalHorizontalCrossingComponent R omega} :
-- imply
  (fkRectOpenGraph R (fkRectForceCutClosed R omega)).connectedComponentMk (fkRectLeftColumn R, fkRectRawPrimalCrossingFirstRow R omega C) = C.1 := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingFirstRow_component R omega C

/--
[fkRectRawPrimalCrossingLastRow_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingLastRow_component_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectRawPrimalHorizontalCrossingComponent R omega} :
-- imply
  (fkRectOpenGraph R (fkRectForceCutClosed R omega)).connectedComponentMk (fkRectLeftColumn R, fkRectRawPrimalCrossingLastRow R omega C) = C.1 := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingLastRow_component R omega C

/--
[fkRectRawPrimalCrossingFirstRow_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingFirstRow_injective_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  Function.Injective (fkRectRawPrimalCrossingFirstRow R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingFirstRow_injective R omega

/--
[fkRectRawPrimalCrossingLastRow_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingLastRow_injective_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  Function.Injective (fkRectRawPrimalCrossingLastRow R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingLastRow_injective R omega

/--
[fkRectRawPrimalCrossingExtremeRow_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingExtremeRow_component_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {side : Bool} :
-- imply
  (fkRectOpenGraph R (fkRectForceCutClosed R omega)).connectedComponentMk (fkRectLeftColumn R, fkRectRawPrimalCrossingExtremeRow R omega C side) = C.1 := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingExtremeRow_component R omega C side

/--
[fkRectRawPrimalCrossing_eq_of_extremeRow_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossing_eq_of_extremeRow_eq_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C D : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {side : Bool}
-- given
  (hrow : fkRectRawPrimalCrossingExtremeRow R omega C side = fkRectRawPrimalCrossingExtremeRow R omega D side) :
-- imply
  C = D := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossing_eq_of_extremeRow_eq R omega C D side hrow

/--
[fkRectOpenGraph_forceCutClosed_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectOpenGraph_forceCutClosed_le_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectOpenGraph R (fkRectForceCutClosed R omega) ≤ fkRectOpenGraph R omega := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_forceCutClosed_le R omega

/--
[fkRectRawPrimalCrossingTorusComponent_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingTorusComponent_mk_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex} :
-- imply
  SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE (fkRectOpenGraph_forceCutClosed_le R omega)) ((fkRectOpenGraph R (fkRectForceCutClosed R omega)).connectedComponentMk x) = (fkRectOpenGraph R omega).connectedComponentMk x := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingTorusComponent_mk R omega x

/--
[fkRectRawPrimalCrossingExtremeDart_label](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingExtremeDart_label_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {side : Bool} :
-- imply
  fkRectMedialDartPrimalLabel R (fkRectRawPrimalCrossingExtremeDart R omega C side) = (fkRectLeftColumn R, fkRectRawPrimalCrossingExtremeRow R omega C side) := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingExtremeDart_label R omega C side

/--
[fkRectRawPrimalCrossing_eq_of_extremeDart_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossing_eq_of_extremeDart_eq_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C D : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {side : Bool}
-- given
  (hdart : fkRectRawPrimalCrossingExtremeDart R omega C side = fkRectRawPrimalCrossingExtremeDart R omega D side) :
-- imply
  C = D := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossing_eq_of_extremeDart_eq R omega C D side hdart

/--
[fkRectZeroTurnRemainderBlackDart_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainderBlackDart_component_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega} :
-- imply
  (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk (fkRectZeroTurnRemainderBlackDart R omega C).1 = C.1 := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainderBlackDart_component R omega C

/--
[fkRectZeroTurnRemainderBlackDart_winding_fst_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainderBlackDart_winding_fst_ne_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega} :
-- imply
  (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega (fkRectZeroTurnRemainderBlackDart R omega C))).1 ≠ 0 := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainderBlackDart_winding_fst_ne_zero R omega C

/--
[fkRectZeroTurnRemainderBlackDart_winding_snd_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainderBlackDart_winding_snd_eq_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega} :
-- imply
  (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega (fkRectZeroTurnRemainderBlackDart R omega C))).2 = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainderBlackDart_winding_snd_eq_zero R omega C

/--
[fkRectZeroTurnRemainderSide_eq_true_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainderSide_eq_true_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega} :
-- imply
  fkRectZeroTurnRemainderSide R omega C = true ↔ 0 < (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega (fkRectZeroTurnRemainderBlackDart R omega C))).1 := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainderSide_eq_true_iff R omega C

/--
[fkRectZeroTurnRemainderSide_eq_false_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainderSide_eq_false_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega} :
-- imply
  fkRectZeroTurnRemainderSide R omega C = false ↔ (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega (fkRectZeroTurnRemainderBlackDart R omega C))).1 < 0 := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainderSide_eq_false_iff R omega C

/--
[fkRectZeroTurnRemainderPrimalComponent_eq_label](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainderPrimalComponent_eq_label_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega} :
-- imply
  fkRectZeroTurnRemainderPrimalComponent R omega C = (fkRectOpenGraph R omega).connectedComponentMk (fkRectMedialDartPrimalLabel R (fkRectZeroTurnRemainderBlackDart R omega C).1) := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainderPrimalComponent_eq_label R omega C

/--
[FKRectZeroTurnCrossingMatches.of_extremeDart_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma of_extremeDart_component_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {side : Bool}
-- given
  (hcomponent : (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk (fkRectRawPrimalCrossingExtremeDart R omega X side) = C.1) :
-- imply
  FKRectZeroTurnCrossingMatches R omega C X := by
-- proof
  apply StatMech.FrontierD.FKRectZeroTurnCrossingMatches.of_extremeDart_component R omega C X side hcomponent

/--
[fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_annulusCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_annulusCharge_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {charge : FKRectZeroTurnAnnulusCharge R omega} :
-- imply
  fkRectZeroTurnCutRemainderCount R omega ≤ 2 * fkRectRawHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_annulusCharge R omega charge

/--
[fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_crossing_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {crossing : FKRectZeroTurnCutRemainderComponent R omega → FKRectRawPrimalHorizontalCrossingComponent R omega}
-- given
  (hunique : ∀ C D, crossing C = crossing D → fkRectZeroTurnRemainderSide R omega C = fkRectZeroTurnRemainderSide R omega D → C = D) :
-- imply
  fkRectZeroTurnCutRemainderCount R omega ≤ 2 * fkRectRawHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_crossing R omega crossing hunique

/--
[fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_clusterMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_clusterMatching_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hexists : ∀ C : FKRectZeroTurnCutRemainderComponent R omega, ∃ X : FKRectRawPrimalHorizontalCrossingComponent R omega, FKRectZeroTurnCrossingMatches R omega C X)
  (hunique : ∀ C D : FKRectZeroTurnCutRemainderComponent R omega, fkRectZeroTurnRemainderPrimalComponent R omega C = fkRectZeroTurnRemainderPrimalComponent R omega D → fkRectZeroTurnRemainderSide R omega C = fkRectZeroTurnRemainderSide R omega D → C = D) :
-- imply
  fkRectZeroTurnCutRemainderCount R omega ≤ 2 * fkRectRawHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_clusterMatching R omega hexists hunique

/--
[fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_anchor_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {crossing : FKRectZeroTurnCutRemainderComponent R omega → FKRectRawPrimalHorizontalCrossingComponent R omega}
  {anchor : FKRectRawPrimalHorizontalCrossingComponent R omega → Bool → FKMedialDart R.medialTorus}
-- given
  (hanchor : ∀ C, (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk (anchor (crossing C) (fkRectZeroTurnRemainderSide R omega C)) = C.1) :
-- imply
  fkRectZeroTurnCutRemainderCount R omega ≤ 2 * fkRectRawHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_anchor R omega crossing anchor hanchor

/--
[fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_extremeDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean)
-/
@[path]
private lemma fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_extremeDart_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {crossing : FKRectZeroTurnCutRemainderComponent R omega → FKRectRawPrimalHorizontalCrossingComponent R omega}
-- given
  (hextreme : ∀ C, (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk (fkRectRawPrimalCrossingExtremeDart R omega (crossing C) (fkRectZeroTurnRemainderSide R omega C)) = C.1) :
-- imply
  fkRectZeroTurnCutRemainderCount R omega ≤ 2 * fkRectRawHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_extremeDart R omega crossing hextreme


-- created on 2026-10-23
