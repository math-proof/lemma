import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryGeometry
open StatMech StatMech.Universality


/--
[fkIsingSquareBoundaryTangent_mul_phase_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryGeometry.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryTangent_mul_phase_sq_eq
  {side : FKIsingSquareBoundarySide} :
-- imply
  fkIsingSquareBoundaryTangent side * fkIsingSquareBoundaryPhase side ^ 2 = 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryTangent_mul_phase_sq side

/--
[FKIsingDobrushinDomain.exists_nonnegative_square_boundary_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryGeometry.lean)
-/
@[path]
private lemma exists_nonnegative_square_boundary_value_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {side : FKIsingSquareBoundarySide}
  {e : M}
-- given
  (hphase : ∀ omega, e ∈ D.exploration omega → D.windingPhase omega e = fkIsingSquareBoundaryPhase side) :
-- imply
  ∃ t : Real, 0 ≤ t ∧ fkIsingSquareBoundaryTangent side * D.fermionicObservable e ^ 2 = (t : Complex) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.exists_nonnegative_square_boundary_value D side e hphase

/--
[fkIsingSquareWired_fermionicObservable_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_fermionicObservable_terminal_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.terminal : FKIsingSquareWiredCarrier n) = 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_fermionicObservable_terminal n hn

/--
[fkIsingSquareWired_terminal_boundary_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_terminal_boundary_square_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  ∃ t : Real, 0 ≤ t ∧ (1 : Complex) * (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.terminal : FKIsingSquareWiredCarrier n) ^ 2 = (t : Complex) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_terminal_boundary_square n hn


-- created on 2026-10-23
