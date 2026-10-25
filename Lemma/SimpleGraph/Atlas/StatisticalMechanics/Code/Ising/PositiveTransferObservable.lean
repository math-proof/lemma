import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.PositiveTransferObservable
open Finset Matrix Filter Topology StatMech StatMech.Ising


/--
[positiveTransfer_endpointObservable_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PositiveTransferObservable.lean)
-/
@[path]
private lemma positiveTransfer_endpointObservable_tendsto_eq
  [Fintype alpha]
  [DecidableEq alpha]
  [Nonempty alpha]
  {A : Matrix alpha alpha Real}
-- given
  (hHerm : A.IsHermitian)
  (hpos : forall i j, 0 < A i j)
  (a ell : alpha -> Real)
  (ha : forall i, 0 < a i)
  (hell : forall i, 0 < ell i)
  (obs : alpha -> Real) :
-- imply
  exists lam : Real, 0 < lam ∧ exists u : EuclideanSpace Real alpha, (forall i, 0 < u i) ∧ norm u = 1 ∧ A *ᵥ (fun i => u i) = lam • (fun i => u i) ∧ Tendsto (fun n : Nat => (∑ i, ell i * obs i * ((A ^ n) *ᵥ a) i) / ∑ i, ell i * ((A ^ n) *ᵥ a) i) atTop (nhds ((∑ i, ell i * obs i * u i) / ∑ i, ell i * u i)) := by
-- proof
  apply StatMech.Ising.positiveTransfer_endpointObservable_tendsto A hHerm hpos a ell ha hell obs

/--
[positiveTransfer_twoBoundary_endpointObservable_common](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PositiveTransferObservable.lean)
-/
@[path]
private lemma positiveTransfer_twoBoundary_endpointObservable_common_eq
  [Fintype alpha]
  [DecidableEq alpha]
  [Nonempty alpha]
  {A : Matrix alpha alpha Real}
-- given
  (hHerm : A.IsHermitian)
  (hpos : forall i j, 0 < A i j)
  (a b ell : alpha -> Real)
  (ha : forall i, 0 < a i)
  (hb : forall i, 0 < b i)
  (hell : forall i, 0 < ell i)
  (obs : alpha -> Real) :
-- imply
  exists m : Real, Tendsto (fun n : Nat => (∑ i, ell i * obs i * ((A ^ n) *ᵥ a) i) / ∑ i, ell i * ((A ^ n) *ᵥ a) i) atTop (nhds m) ∧ Tendsto (fun n : Nat => (∑ i, ell i * obs i * ((A ^ n) *ᵥ b) i) / ∑ i, ell i * ((A ^ n) *ᵥ b) i) atTop (nhds m) := by
-- proof
  apply StatMech.Ising.positiveTransfer_twoBoundary_endpointObservable_common A hHerm hpos a b ell ha hb hell obs


-- created on 2026-10-23
