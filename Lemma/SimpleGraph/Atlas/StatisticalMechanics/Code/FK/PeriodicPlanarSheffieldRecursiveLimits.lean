import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRecursiveLimits
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.exists_cofinalNormalBoundaryBandFamilies_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRecursiveLimits.lean)
-/
@[path]
private lemma exists_cofinalNormalBoundaryBandFamilies_bounded_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  exists (p : Nat -> Real) (family : forall m, E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)), Tendsto p atTop (nhds 1) /\ (forall m, p m <= 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_cofinalNormalBoundaryBandFamilies_bounded E mu hFKG hTI hunique

/--
[PeriodicPlaneEmbedding.exists_uniformBoundaryBandRadius_with_boundedCofinalConnectorSchedule](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRecursiveLimits.lean)
-/
@[path]
private lemma exists_uniformBoundaryBandRadius_with_boundedCofinalConnectorSchedule_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  exists (radius : Nat -> Nat) (p : Nat -> Real) (family : forall m, E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)), E.UniformBoundaryBandCrossingRadius mu radius /\ Tendsto p atTop (nhds 1) /\ (forall m, p m <= 1) /\ forall m, (family m).AlignedMarginSchedule E (fun _ => E.connectorMarginRequirement (radius m)) (fun _ => E.connectorMarginRequirement (radius m)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformBoundaryBandRadius_with_boundedCofinalConnectorSchedule E mu hFKG hTI hunique

/--
[PeriodicPlaneEmbedding.exists_recursiveAlignedSharedLevelSteps_with_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRecursiveLimits.lean)
-/
@[path]
private lemma exists_recursiveAlignedSharedLevelSteps_with_limits_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {family : forall m, E.NormalBoundaryBandFamily mu (S m) (p m)}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (S : Nat -> Finset V)
  (p : Nat -> Real)
  (hp : Tendsto p atTop (nhds 1))
  (hp_le_one : forall m, p m <= 1)
  (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat) :
-- imply
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real) exists state : Nat -> Nat × Nat, exists steps : forall n, E.AlignedSharedLevelStep mu S p family verticalRequirement horizontalRequirement (state n).1 (state n).2 (epsilon n) (epsilon n), state 0 = (0, 0) /\ (forall n, state (n + 1) = ((steps n).scale + 1, (steps n).nextConnector)) /\ Tendsto (fun n => (steps n).scale) atTop atTop /\ Tendsto (fun n => p (steps n).scale) atTop (nhds 1) /\ Tendsto (fun n => mu.real (E.rectSideConnectionEvent (-(steps n).extent : Real) (steps n).extent (-(steps n).extent : Real) (steps n).extent ((steps n).bottom : Set V) (E.rectBottomBoundaryVertices (-(steps n).extent : Real) (steps n).extent (-(steps n).extent : Real) (steps n).extent))) atTop (nhds 1) /\ Tendsto (fun n => mu.real (E.rectSideConnectionEvent (-(steps n).extent : Real) (steps n).extent (-(steps n).extent : Real) (steps n).extent ((steps n).top : Set V) (E.rectTopBoundaryVertices (-(steps n).extent : Real) (steps n).extent (-(steps n).extent : Real) (steps n).extent))) atTop (nhds 1) /\ Tendsto (fun n => mu.real (E.rectSideConnectionEvent (-(steps n).extent : Real) (steps n).extent (-(steps n).extent : Real) (steps n).extent ((steps n).left : Set V) (E.rectLeftBoundaryVertices (-(steps n).extent : Real) (steps n).extent (-(steps n).extent : Real) (steps n).extent))) atTop (nhds 1) /\ Tendsto (fun n => mu.real (E.rectSideConnectionEvent (-(steps n).extent : Real) (steps n).extent (-(steps n).extent : Real) (steps n).extent ((steps n).right : Set V) (E.rectRightBoundaryVertices (-(steps n).extent : Real) (steps n).extent (-(steps n).extent : Real) (steps n).extent))) atTop (nhds 1) /\ Tendsto (fun n => mu.real (P.pairMergeErrorUnion (steps n).bottom (steps n).top (steps n).nextConnector)) atTop (nhds 0) /\ Tendsto (fun n => mu.real (P.pairMergeErrorUnion (steps n).left (steps n).right (steps n).nextConnector)) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_recursiveAlignedSharedLevelSteps_with_limits E mu hTI hunique S p family hp hp_le_one verticalRequirement horizontalRequirement

/--
[PeriodicPlaneEmbedding.exists_uniformRadius_recursiveAlignedSharedLevelSteps_with_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRecursiveLimits.lean)
-/
@[path]
private lemma exists_uniformRadius_recursiveAlignedSharedLevelSteps_with_limits_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real) exists (radius : Nat -> Nat) (p : Nat -> Real) (family : forall m, E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)) (state : Nat -> Nat × Nat), exists steps : forall n, E.AlignedSharedLevelStep mu (fun m => P.orbitBox m) p family (fun m _ => E.connectorMarginRequirement (radius m)) (fun m _ => E.connectorMarginRequirement (radius m)) (state n).1 (state n).2 (epsilon n) (epsilon n), E.UniformBoundaryBandCrossingRadius mu radius /\ Tendsto p atTop (nhds 1) /\ (forall m, p m <= 1) /\ state 0 = (0, 0) /\ (forall n, state (n + 1) = ((steps n).scale + 1, (steps n).nextConnector)) /\ Tendsto (fun n => (steps n).scale) atTop atTop /\ Tendsto (fun n => p (steps n).scale) atTop (nhds 1) /\ Tendsto (fun n => mu.real (E.rectSideConnectionEvent (-(steps n).extent : Real) (steps n).extent (-(steps n).extent : Real) (steps n).extent ((steps n).bottom : Set V) (E.rectBottomBoundaryVertices (-(steps n).extent : Real) (steps n).extent (-(steps n).extent : Real) (steps n).extent))) atTop (nhds 1) /\ Tendsto (fun n => mu.real (E.rectSideConnectionEvent (-(steps n).extent : Real) (steps n).extent (-(steps n).extent : Real) (steps n).extent ((steps n).top : Set V) (E.rectTopBoundaryVertices (-(steps n).extent : Real) (steps n).extent (-(steps n).extent : Real) (steps n).extent))) atTop (nhds 1) /\ Tendsto (fun n => mu.real (E.rectSideConnectionEvent (-(steps n).extent : Real) (steps n).extent (-(steps n).extent : Real) (steps n).extent ((steps n).left : Set V) (E.rectLeftBoundaryVertices (-(steps n).extent : Real) (steps n).extent (-(steps n).extent : Real) (steps n).extent))) atTop (nhds 1) /\ Tendsto (fun n => mu.real (E.rectSideConnectionEvent (-(steps n).extent : Real) (steps n).extent (-(steps n).extent : Real) (steps n).extent ((steps n).right : Set V) (E.rectRightBoundaryVertices (-(steps n).extent : Real) (steps n).extent (-(steps n).extent : Real) (steps n).extent))) atTop (nhds 1) /\ Tendsto (fun n => mu.real (P.pairMergeErrorUnion (steps n).bottom (steps n).top (steps n).nextConnector)) atTop (nhds 0) /\ Tendsto (fun n => mu.real (P.pairMergeErrorUnion (steps n).left (steps n).right (steps n).nextConnector)) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformRadius_recursiveAlignedSharedLevelSteps_with_limits E mu hFKG hTI hunique


-- created on 2026-10-23
