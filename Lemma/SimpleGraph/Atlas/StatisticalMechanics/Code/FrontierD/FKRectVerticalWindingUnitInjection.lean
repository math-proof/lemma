import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingUnitInjection
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectBlackBoundaryCycleInPrimalCluster_iff_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingUnitInjection.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCycleInPrimalCluster_iff_component_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex}
  {C : FKRectConfigurationBlackBoundaryCycle R omega} :
-- imply
  fkRectBlackBoundaryCycleInPrimalCluster R omega x C ↔ fkRectBlackBoundaryCyclePrimalComponent R omega C = (fkRectOpenGraph R omega).connectedComponentMk x := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCycleInPrimalCluster_iff_component R omega x C

/--
[fkRectBlackBoundaryCycleWinding_det_eq_zero_of_not_componentHasNet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingUnitInjection.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCycleWinding_det_eq_zero_of_not_componentHasNet_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent}
  {C D : FKRectConfigurationBlackBoundaryCycle R omega}
-- given
  (hnoNet : ¬ FKRectPrimalComponentHasNet R omega K)
  (hC : fkRectBlackBoundaryCycleInPrimalCluster R omega K.out C)
  (hD : fkRectBlackBoundaryCycleInPrimalCluster R omega K.out D) :
-- imply
  (fkRectBlackBoundaryCycleWinding R omega C).1 * (fkRectBlackBoundaryCycleWinding R omega D).2 - (fkRectBlackBoundaryCycleWinding R omega C).2 * (fkRectBlackBoundaryCycleWinding R omega D).1 = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCycleWinding_det_eq_zero_of_not_componentHasNet R omega K hnoNet hC hD

/--
[card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_of_sameSignUnique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingUnitInjection.lean)
-/
@[path]
private lemma card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_of_sameSignUnique_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent}
-- given
  (hnoNet : ¬ FKRectPrimalComponentHasNet R omega K)
  (hsame : ∀ C D : FKRectConfigurationBlackBoundaryCycle R omega, C ∈ fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out → D ∈ fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out → (0 < (fkRectBlackBoundaryCycleWinding R omega C).1 * (fkRectBlackBoundaryCycleWinding R omega D).1 ∨ 0 < (fkRectBlackBoundaryCycleWinding R omega C).2 * (fkRectBlackBoundaryCycleWinding R omega D).2) → C = D) :
-- imply
  (fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out).card ≤ 2 := by
-- proof
  apply StatMech.FrontierD.card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_of_sameSignUnique R omega K hnoNet hsame

/--
[eq_of_sum_ite_eq_zero_of_card_nonzero_le_two_of_snd_mul_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingUnitInjection.lean)
-/
@[path]
private lemma eq_of_sum_ite_eq_zero_of_card_nonzero_le_two_of_snd_mul_pos_eq
  [Fintype D]
  [DecidablePred p]
  {w : D → Int × Int}
  {a b : D}
-- given
  (p : D → Prop)
  (hsum : (∑ d : D, if p d then w d else 0) = 0)
  (hcard : (Finset.univ.filter fun d => p d ∧ w d ≠ 0).card ≤ 2)
  (ha : p a)
  (hb : p b)
  (hsign : 0 < (w a).2 * (w b).2) :
-- imply
  a = b := by
-- proof
  apply StatMech.FrontierD.eq_of_sum_ite_eq_zero_of_card_nonzero_le_two_of_snd_mul_pos p w hsum hcard ha hb hsign

/--
[fkRectBlackBoundaryCycle_eq_of_card_nonzero_le_two_of_snd_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingUnitInjection.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCycle_eq_of_card_nonzero_le_two_of_snd_pos_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex}
  {C D : FKRectConfigurationBlackBoundaryCycle R omega}
-- given
  (hcard : (fkRectPrimalClusterNonzeroBoundaryCycles R omega x).card ≤ 2)
  (hC : fkRectBlackBoundaryCycleInPrimalCluster R omega x C)
  (hD : fkRectBlackBoundaryCycleInPrimalCluster R omega x D)
  (hCpos : 0 < (fkRectBlackBoundaryCycleWinding R omega C).2)
  (hDpos : 0 < (fkRectBlackBoundaryCycleWinding R omega D).2) :
-- imply
  C = D := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCycle_eq_of_card_nonzero_le_two_of_snd_pos R omega x hcard hC hD hCpos hDpos

/--
[fkRectMedialBoundaryPrimalTraceBetween_winding_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingUnitInjection.lean)
-/
@[path]
private lemma fkRectMedialBoundaryPrimalTraceBetween_winding_snd_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus}
  {a b : Nat}
-- given
  (hab : a ≤ b) :
-- imply
  (fkRectWalkWinding R (fkRectMedialBoundaryPrimalTraceBetween R omega d a b hab)).2 = (fkRectMedialBoundaryPrimalSeamTrace R (fkRectConfigurationToMedialPairing R omega) d b).2 - (fkRectMedialBoundaryPrimalSeamTrace R (fkRectConfigurationToMedialPairing R omega) d a).2 := by
-- proof
  apply StatMech.FrontierD.fkRectMedialBoundaryPrimalTraceBetween_winding_snd R omega d a b hab

/--
[fkRectBlackBoundaryUnitPlateauEntry_level](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingUnitInjection.lean)
-/
@[path]
private lemma fkRectBlackBoundaryUnitPlateauEntry_level_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {j : Fin (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat}
-- given
  (hpos : 0 < (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2) :
-- imply
  let a := (fkRectBlackBoundaryUnitPlateauEndpoints R omega d hpos j).1 (fkRectMedialBoundaryPrimalSeamTrace R (fkRectConfigurationToMedialPairing R omega) d.1 a).2 = (j.val : Int) + 1 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryUnitPlateauEntry_level R omega d hpos j

/--
[fkRectBlackBoundaryUnitPlateauEntry_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingUnitInjection.lean)
-/
@[path]
private lemma fkRectBlackBoundaryUnitPlateauEntry_strictMono_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {j k : Fin (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat}
-- given
  (hpos : 0 < (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
  (hjk : j < k) :
-- imply
  (fkRectBlackBoundaryUnitPlateauEndpoints R omega d hpos j).1 < (fkRectBlackBoundaryUnitPlateauEndpoints R omega d hpos k).1 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryUnitPlateauEntry_strictMono R omega d hpos hjk

/--
[fkRectBlackBoundaryUnitCutComponent_torusComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingUnitInjection.lean)
-/
@[path]
private lemma fkRectBlackBoundaryUnitCutComponent_torusComponent_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {j : Fin (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat}
-- given
  (hpos : 0 < (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2) :
-- imply
  fkRectHorizontalCutComponentTorusComponent R omega (fkRectBlackBoundaryUnitCutComponent R omega d hpos j) = (fkRectOpenGraph R omega).connectedComponentMk (fkRectMedialDartPrimalLabel R d.1) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryUnitCutComponent_torusComponent R omega d hpos j

/--
[fkRectPrimalComponentHasNet_of_boundaryUnitCutComponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingUnitInjection.lean)
-/
@[path]
private lemma fkRectPrimalComponentHasNet_of_boundaryUnitCutComponent_eq_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent}
  {d : FKMedialBlackDart R.medialTorus}
  {j k : Fin (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat}
-- given
  (hdK : (fkRectOpenGraph R omega).connectedComponentMk (fkRectMedialDartPrimalLabel R d.1) = K)
  (hprimitive : FKRectPrimitiveWinding (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)))
  (hpos : 0 < (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
  (hjk : j < k)
  (heq : fkRectBlackBoundaryUnitCutComponent R omega d hpos j = fkRectBlackBoundaryUnitCutComponent R omega d hpos k) :
-- imply
  FKRectPrimalComponentHasNet R omega K := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalComponentHasNet_of_boundaryUnitCutComponent_eq R omega K d hdK hprimitive hpos hjk heq

/--
[nonempty_boundaryUnitEmbedding_horizontalCutCrossingInFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingUnitInjection.lean)
-/
@[path]
private lemma nonempty_boundaryUnitEmbedding_horizontalCutCrossingInFiber_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent}
  {d : FKMedialBlackDart R.medialTorus}
-- given
  (hdK : (fkRectOpenGraph R omega).connectedComponentMk (fkRectMedialDartPrimalLabel R d.1) = K)
  (hprimitive : FKRectPrimitiveWinding (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)))
  (hpos : 0 < (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
  (hnoNet : ¬ FKRectPrimalComponentHasNet R omega K) :
-- imply
  Nonempty (Fin (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat ↪ FKRectHorizontalCutCrossingInFiber R omega K) := by
-- proof
  apply StatMech.FrontierD.nonempty_boundaryUnitEmbedding_horizontalCutCrossingInFiber R omega K d hdK hprimitive hpos hnoNet

/--
[nonempty_positiveBoundaryUnitEmbedding_of_card_nonzero_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingUnitInjection.lean)
-/
@[path]
private lemma nonempty_positiveBoundaryUnitEmbedding_of_card_nonzero_le_two_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent}
-- given
  (hcard : (fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out).card ≤ 2)
  (hprimitive : ∀ d : FKMedialBlackDart R.medialTorus, 0 < (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 → FKRectPrimitiveWinding (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)))
  (hnoNet : ¬ FKRectPrimalComponentHasNet R omega K) :
-- imply
  Nonempty (FKRectPositiveBoundaryUnit R omega K ↪ FKRectHorizontalCutCrossingInFiber R omega K) := by
-- proof
  apply StatMech.FrontierD.nonempty_positiveBoundaryUnitEmbedding_of_card_nonzero_le_two R omega K hcard hprimitive hnoNet

/--
[rankOnePositiveBoundaryCutFiberBound_of_card_nonzero_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingUnitInjection.lean)
-/
@[path]
private lemma rankOnePositiveBoundaryCutFiberBound_of_card_nonzero_le_two_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hcard : ∀ K : (fkRectOpenGraph R omega).ConnectedComponent, ¬ FKRectPrimalComponentHasNet R omega K → (fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out).card ≤ 2)
  (hprimitive : ∀ d : FKMedialBlackDart R.medialTorus, 0 < (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 → FKRectPrimitiveWinding (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d))) :
-- imply
  FKRectRankOnePositiveVerticalBoundaryCutFiberBound R omega := by
-- proof
  apply StatMech.FrontierD.rankOnePositiveBoundaryCutFiberBound_of_card_nonzero_le_two R omega hcard hprimitive


-- created on 2026-10-23
