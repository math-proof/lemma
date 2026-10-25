import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldConnectorReadyCommonSquare
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.exists_connectorReadyCommonSquareData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldConnectorReadyCommonSquare.lean)
-/
@[path]
private lemma exists_connectorReadyCommonSquareData_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (radius : Nat -> Nat) :
-- imply
  Nonempty (E.ConnectorReadyCommonSquareData mu radius) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_connectorReadyCommonSquareData E mu hFKG hTI hunique radius

/--
[PeriodicPlaneEmbedding.exists_uniformConnectorRadius_with_commonSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldConnectorReadyCommonSquare.lean)
-/
@[path]
private lemma exists_uniformConnectorRadius_with_commonSquare_eq
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
  exists radius : Nat -> Nat, E.UniformConnectorCrossingRadius mu radius ∧ Nonempty (E.ConnectorReadyCommonSquareData mu radius) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformConnectorRadius_with_commonSquare E mu hFKG hTI hunique

/--
[exists_matchedPreferenceGrid_connectorContainment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldConnectorReadyCommonSquare.lean)
-/
@[path]
private lemma exists_matchedPreferenceGrid_connectorContainment_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {radius radiusDual : Nat -> Nat}
  {primal : E.ConnectorReadyCommonSquareData mu radius}
  {dual : Edual.ConnectorReadyCommonSquareData muDual radiusDual} :
-- imply
  let commonM : Nat -> Nat := fun n => max (primal.M n) (dual.M n) exists extentX extentY : Nat -> Nat, (forall n, 0 < primal.baseRight n 0 + (extentX n : Int) - primal.baseLeft n 0) ∧ (forall n, 0 < dual.baseRight n 0 + (extentX n : Int) - dual.baseLeft n 0) ∧ (forall n, 0 < primal.baseTop n 1 + (extentY n : Int) - primal.baseBottom n 1) ∧ (forall n, 0 < dual.baseTop n 1 + (extentY n : Int) - dual.baseBottom n 1) ∧ (forall n (v : PreferenceGridVertex (boundaryGridWidth (extentX n) (primal.baseLeft n) (primal.baseRight n)) (boundaryGridHeight (extentY n) (primal.baseBottom n) (primal.baseTop n))), P.shift (boundaryGridBase (primal.baseLeft n) (primal.baseBottom n) + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆ E.rectVertices (-(commonM n : Real)) (commonM n + extentX n : Real) (-(commonM n : Real)) (commonM n + extentY n : Real)) ∧ (forall n (v : PreferenceGridVertex (boundaryGridWidth (extentX n) (dual.baseLeft n) (dual.baseRight n)) (boundaryGridHeight (extentY n) (dual.baseBottom n) (dual.baseTop n))), Pdual.shift (boundaryGridBase (dual.baseLeft n) (dual.baseBottom n) + preferenceGridSite v) '' (Pdual.orbitBox (Pdual.bufferedRadius (radiusDual n)) : Set W) ⊆ Edual.rectVertices (-(commonM n : Real)) (commonM n + extentX n : Real) (-(commonM n : Real)) (commonM n + extentY n : Real)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_matchedPreferenceGrid_connectorContainment E Edual primal dual


-- created on 2026-10-23
