import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
open StatMech StatMech.Universality


/--
[fkIsingSquareWiredDirectedTangentCode_boundaryDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredTangentCode.lean)
-/
@[path]
private lemma fkIsingSquareWiredDirectedTangentCode_boundaryDart_eq
  {n : Nat}
  {i : FKIsingSquareWiredBoundaryDartIndex n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredDirectedTangentCode n hn (.bond (fkIsingSquareWiredBoundaryDart n hn i)) = match i with := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredDirectedTangentCode_boundaryDart n hn i


-- created on 2026-10-23
