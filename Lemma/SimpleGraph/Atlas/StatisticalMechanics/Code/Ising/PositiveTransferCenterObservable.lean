import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.PositiveTransferCenterObservable
open Finset Matrix Filter Topology StatMech StatMech.Ising


/--
[hermitian_twoTail_contraction_eq_sum_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PositiveTransferCenterObservable.lean)
-/
@[path]
private lemma hermitian_twoTail_contraction_eq_sum_sq_eq
  [Fintype alpha]
  [DecidableEq alpha]
  [Nonempty alpha]
  {A : Matrix alpha alpha Real}
  {n : Nat}
-- given
  (hHerm : A.IsHermitian)
  (a : alpha -> Real) :
-- imply
  (∑ i, a i * ((A ^ (2 * n)) *ᵥ a) i) = ∑ i, ((A ^ n) *ᵥ a) i ^ 2 := by
-- proof
  apply StatMech.Ising.hermitian_twoTail_contraction_eq_sum_sq A hHerm a n

/--
[positiveTransfer_centerObservable_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PositiveTransferCenterObservable.lean)
-/
@[path]
private lemma positiveTransfer_centerObservable_tendsto_eq
  [Fintype alpha]
  [DecidableEq alpha]
  [Nonempty alpha]
  {A : Matrix alpha alpha Real}
-- given
  (hHerm : A.IsHermitian)
  (hpos : forall i j, 0 < A i j)
  (a : alpha -> Real)
  (ha : forall i, 0 < a i)
  (obs : alpha -> Real) :
-- imply
  exists lam : Real, 0 < lam ∧ exists u : EuclideanSpace Real alpha, (forall i, 0 < u i) ∧ norm u = 1 ∧ A *ᵥ (fun i => u i) = lam • (fun i => u i) ∧ Tendsto (fun n : Nat => (∑ i, obs i * ((A ^ n) *ᵥ a) i ^ 2) / ∑ i, ((A ^ n) *ᵥ a) i ^ 2) atTop (nhds ((∑ i, obs i * (u i) ^ 2) / ∑ i, (u i) ^ 2)) := by
-- proof
  apply StatMech.Ising.positiveTransfer_centerObservable_tendsto A hHerm hpos a ha obs


-- created on 2026-10-23
