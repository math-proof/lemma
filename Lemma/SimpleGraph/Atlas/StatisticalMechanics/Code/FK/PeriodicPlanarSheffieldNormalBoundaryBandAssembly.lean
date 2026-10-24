import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldNormalBoundaryBandAssembly
open MeasureTheory StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[exists_matched_commonSquareNormalBoundaryBandData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNormalBoundaryBandAssembly.lean)
-/
@[path]
private lemma exists_matched_commonSquareNormalBoundaryBandData_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {margin : Nat}
  {p pDual : Real}
  {primal : E.NormalBoundaryBandSeed mu S margin p}
  {dual : Edual.NormalBoundaryBandSeed muDual Sdual margin pDual}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual) :
-- imply
  ∃ M : Nat, Nonempty (E.CommonSquareNormalBoundaryBandData mu S margin M p) ∧ Nonempty (Edual.CommonSquareNormalBoundaryBandData muDual Sdual margin M pDual) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_matched_commonSquareNormalBoundaryBandData E Edual mu muDual hTI hTIDual primal dual


-- created on 2026-10-23
