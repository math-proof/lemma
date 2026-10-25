import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonSquareEnlarge
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.ConnectorReadyCommonSquareData.exists_enlarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonSquareEnlarge.lean)
-/
@[path]
private lemma exists_enlarge_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {radius : Nat -> Nat}
  {data : E.ConnectorReadyCommonSquareData mu radius}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (M' : Nat -> Nat)
  (hM : forall n, data.M n <= M' n) :
-- imply
  exists enlarged : E.ConnectorReadyCommonSquareData mu radius, enlarged.M = M' := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.ConnectorReadyCommonSquareData.exists_enlarge E hTI data M' hM

/--
[exists_commonHalfWidth_connectorReadyData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonSquareEnlarge.lean)
-/
@[path]
private lemma exists_commonHalfWidth_connectorReadyData_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {radius radiusDual : Nat -> Nat}
  {primal : E.ConnectorReadyCommonSquareData mu radius}
  {dual : Edual.ConnectorReadyCommonSquareData muDual radiusDual}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual) :
-- imply
  let commonM : Nat -> Nat := fun n => max (primal.M n) (dual.M n) exists primal' : E.ConnectorReadyCommonSquareData mu radius, exists dual' : Edual.ConnectorReadyCommonSquareData muDual radiusDual, primal'.M = commonM ∧ dual'.M = commonM := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_commonHalfWidth_connectorReadyData E Edual hTI hTIDual primal dual


-- created on 2026-10-23
