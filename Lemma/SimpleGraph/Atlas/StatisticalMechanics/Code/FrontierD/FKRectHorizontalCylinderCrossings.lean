import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part6
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectHorizontalCylinderCrossingClusterCount_eq_horizontalCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderCrossingClusterCount_eq_horizontalCut_eq
  {R : FKRectTorus}
  {eta : FKRectHorizontalCutClosedConfig R} :
-- imply
  fkRectHorizontalCylinderCrossingClusterCount R (fkRectHorizontalCutClosedEdgeConfigEquiv R eta).1 = fkRectHorizontalCutPrimalCrossingClusterCount R eta.1 := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderCrossingClusterCount_eq_horizontalCut R eta

/--
[fkRectHorizontalCylinderCrossingClusterCount_force_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderCrossingClusterCount_force_eq_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectHorizontalCylinderCrossingClusterCount R (fkRectHorizontalCutClosedEdgeConfigEquiv R ⟨fkRectForceHorizontalCutClosed R omega, fkRectHorizontalCutClosedConfiguration_force R omega⟩).1 = fkRectHorizontalCutPrimalCrossingClusterCount R (fkRectForceHorizontalCutClosed R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderCrossingClusterCount_force_eq R omega

/--
[fkRectHorizontalCylinderCrossingTail_iff_horizontalCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderCrossingTail_iff_horizontalCut_eq
  {R : FKRectTorus}
  {eta : FKRectHorizontalCutClosedConfig R}
  {n : Nat} :
-- imply
  n ≤ fkRectHorizontalCylinderCrossingClusterCount R (fkRectHorizontalCutClosedEdgeConfigEquiv R eta).1 ↔ n ≤ fkRectHorizontalCutPrimalCrossingClusterCount R eta.1 := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderCrossingTail_iff_horizontalCut R eta n

/--
[fkRectHorizontalCylinderCrossingRepresentative_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderCrossingRepresentative_component_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {C : {C : (FK.openSub (fkRectHorizontalCylinderGraph R) rho).ConnectedComponent // FKRectHorizontalCylinderCrossingComponent R rho C}} :
-- imply
  (FK.openSub (fkRectHorizontalCylinderGraph R) rho).connectedComponentMk (fkRectHorizontalCylinderCrossingRepresentative R rho C, fkRectBottomRow R) = C.1 := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderCrossingRepresentative_component R rho C

/--
[fkRectHorizontalCylinderCrossingRepresentative_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderCrossingRepresentative_source_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {C : {C : (FK.openSub (fkRectHorizontalCylinderGraph R) rho).ConnectedComponent // FKRectHorizontalCylinderCrossingComponent R rho C}} :
-- imply
  FKRectHorizontalCylinderCrossingSource R rho (fkRectHorizontalCylinderCrossingRepresentative R rho C) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderCrossingRepresentative_source R rho C

/--
[fkRectHorizontalCylinderCrossingRepresentative_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderCrossingRepresentative_injective_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)} :
-- imply
  Function.Injective (fkRectHorizontalCylinderCrossingRepresentative R rho) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderCrossingRepresentative_injective R rho

/--
[card_fkRectHorizontalCylinderCrossingRepresentativeIndices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean)
-/
@[path]
private lemma card_fkRectHorizontalCylinderCrossingRepresentativeIndices_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)} :
-- imply
  (fkRectHorizontalCylinderCrossingRepresentativeIndices R rho).card = fkRectHorizontalCylinderCrossingClusterCount R rho := by
-- proof
  apply StatMech.FrontierD.card_fkRectHorizontalCylinderCrossingRepresentativeIndices R rho

/--
[fkRectHorizontalCylinderCrossingRepresentativeIndices_subset_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderCrossingRepresentativeIndices_subset_sources_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)} :
-- imply
  ∀ x ∈ fkRectHorizontalCylinderCrossingRepresentativeIndices R rho, FKRectHorizontalCylinderCrossingSource R rho x := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderCrossingRepresentativeIndices_subset_sources R rho

/--
[eq_of_horizontalCylinder_representatives_of_component_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean)
-/
@[path]
private lemma eq_of_horizontalCylinder_representatives_of_component_eq_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {x y : Fin R.width}
-- given
  (hx : x ∈ fkRectHorizontalCylinderCrossingRepresentativeIndices R rho)
  (hy : y ∈ fkRectHorizontalCylinderCrossingRepresentativeIndices R rho)
  (hcomponent : (FK.openSub (fkRectHorizontalCylinderGraph R) rho).connectedComponentMk (x, fkRectBottomRow R) = (FK.openSub (fkRectHorizontalCylinderGraph R) rho).connectedComponentMk (y, fkRectBottomRow R)) :
-- imply
  x = y := by
-- proof
  apply StatMech.FrontierD.eq_of_horizontalCylinder_representatives_of_component_eq R rho hx hy hcomponent

/--
[fkRectHorizontalCylinderCrossingTarget_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderCrossingTarget_reachable_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {x : Fin R.width}
-- given
  (hx : FKRectHorizontalCylinderCrossingSource R rho x) :
-- imply
  (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable (x, fkRectBottomRow R) (fkRectHorizontalCylinderCrossingTarget R rho x, fkRectTopRow R) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderCrossingTarget_reachable R rho hx

/--
[exists_fkRectHorizontalCylinderDistinctPairedWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean)
-/
@[path]
private lemma exists_fkRectHorizontalCylinderDistinctPairedWitness_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {n : Nat}
-- given
  (hn : n <= fkRectHorizontalCylinderCrossingClusterCount R rho) :
-- imply
  ∃ S : Finset (Fin R.width), S.card = n ∧ FKRectHorizontalCylinderDistinctPairedWitness R (fkRectHorizontalCylinderCrossingTarget R rho) S rho := by
-- proof
  apply StatMech.FrontierD.exists_fkRectHorizontalCylinderDistinctPairedWitness R rho n hn

/--
[fkRectHorizontalCylinderCrossingTail_le_choose_mul_pairCount_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderCrossingTail_le_choose_mul_pairCount_mul_eq
  {R : FKRectTorus}
  {n : Nat}
  {a : Real}
-- given
  (mu : ConfigSpace (Sym2 R.Vertex) -> Real)
  (hmu : ∀ rho, 0 <= mu rho)
  (hmass : ∀ S : Finset (Fin R.width), S.card = n -> ∀ pair : Fin R.width -> Fin R.width, StatMech.Probability.finiteEventMass mu {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair S rho} <= a) :
-- imply
  StatMech.Probability.finiteEventMass mu {rho | n <= fkRectHorizontalCylinderCrossingClusterCount R rho} <= Nat.choose R.width n * R.width ^ R.width * a := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderCrossingTail_le_choose_mul_pairCount_mul R mu hmu n a hmass

/--
[fkRectHorizontalCutClosedConfiguration_force_eq_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean)
-/
@[path]
private lemma fkRectHorizontalCutClosedConfiguration_force_eq_self_eq
  {R : FKRectTorus}
  {eta : R.Configuration}
-- given
  (hclosed : FKRectHorizontalCutClosedConfiguration R eta) :
-- imply
  fkRectForceHorizontalCutClosed R eta = eta := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCutClosedConfiguration_force_eq_self R eta hclosed

/--
[openSub_ecz_closeOff_horizontalCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean)
-/
@[path]
private lemma openSub_ecz_closeOff_horizontalCylinder_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)} :
-- imply
  FK.openSub (fkRectHorizontalCylinderGraph R) (FK.ecz_closeOff (fkRectHorizontalCylinderGraph R) rho).1 = FK.openSub (fkRectHorizontalCylinderGraph R) rho := by
-- proof
  apply StatMech.FrontierD.openSub_ecz_closeOff_horizontalCylinder R rho

/--
[FKRectHorizontalCylinderDistinctPairedWitness.congr_openSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean)
-/
@[path]
private lemma congr_openSub_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.width)}
  {rho sigma : ConfigSpace (Sym2 R.Vertex)}
-- given
  (pair : Fin R.width -> Fin R.width)
  (hgraph : FK.openSub (fkRectHorizontalCylinderGraph R) rho = FK.openSub (fkRectHorizontalCylinderGraph R) sigma) :
-- imply
  FKRectHorizontalCylinderDistinctPairedWitness R pair S rho ↔ FKRectHorizontalCylinderDistinctPairedWitness R pair S sigma := by
-- proof
  apply StatMech.FrontierD.FKRectHorizontalCylinderDistinctPairedWitness.congr_openSub R pair S hgraph

/--
[fkRectHorizontalCylinderStablePairedWitness_edgeEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderStablePairedWitness_edgeEvent_eq_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.width)}
-- given
  (pair : Fin R.width -> Fin R.width) :
-- imply
  FK.ecz_closeOff (fkRectHorizontalCylinderGraph R) ⁻¹' fkRectHorizontalCylinderEdgeEvent R {eta | FKRectHorizontalCylinderStablePairedWitnessCore R pair S eta} = {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair S rho} := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderStablePairedWitness_edgeEvent_eq R pair S

/--
[fkRectCriticalHorizontalCut_stablePairedWitness_eq_finiteEventMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean)
-/
@[path]
private lemma fkRectCriticalHorizontalCut_stablePairedWitness_eq_finiteEventMass_eq
  {R : FKRectTorus}
  {q : Real}
  {S : Finset (Fin R.width)}
-- given
  (pair : Fin R.width -> Fin R.width)
  (hq : 1 <= q) :
-- imply
  fkRectCriticalHorizontalCutEventMass R q {eta | FKRectHorizontalCylinderStablePairedWitnessCore R pair S eta} = StatMech.Probability.finiteEventMass (FK.fkProb (fkRectHorizontalCylinderGraph R) (fkRectCriticalP q) q) {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair S rho} := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalHorizontalCut_stablePairedWitness_eq_finiteEventMass R pair hq S


-- created on 2026-10-23
