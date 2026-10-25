import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldGlobalAssembly
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[exists_adjacent_balanced_height_sequence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldGlobalAssembly.lean)
-/
@[path]
private lemma exists_adjacent_balanced_height_sequence_eq
  {K : Nat → Nat}
-- given
  (horizontal vertical : Nat → Nat → Real)
  (hstart : ∀ n, horizontal n 0 ≤ vertical n 0)
  (hend : ∀ n, vertical n (K n + 1) ≤ horizontal n (K n + 1)) :
-- imply
  ∃ k : Nat → Nat, ∀ n, k n < K n + 1 ∧ horizontal n (k n) ≤ vertical n (k n) ∧ vertical n (k n + 1) ≤ horizontal n (k n + 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_adjacent_balanced_height_sequence horizontal vertical K hstart hend

/--
[exists_adjacent_approximate_balanced_height_sequence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldGlobalAssembly.lean)
-/
@[path]
private lemma exists_adjacent_approximate_balanced_height_sequence_eq
  {error : Nat → Real}
  {K : Nat → Nat}
-- given
  (horizontal vertical : Nat → Nat → Real)
  (herror : ∀ n, 0 ≤ error n)
  (hstart : ∀ n, horizontal n 0 ≤ vertical n 0 + error n)
  (hend : ∀ n, vertical n (K n + 1) ≤ horizontal n (K n + 1) + error n) :
-- imply
  ∃ k : Nat → Nat, ∀ n, k n < K n + 1 ∧ horizontal n (k n) ≤ vertical n (k n) + error n ∧ vertical n (k n + 1) ≤ horizontal n (k n + 1) + error n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_adjacent_approximate_balanced_height_sequence horizontal vertical error K herror hstart hend

/--
[approximate_balanced_height_sequence_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldGlobalAssembly.lean)
-/
@[path]
private lemma approximate_balanced_height_sequence_contradiction_eq
-- given
  (horizontal vertical : Nat -> Nat -> Real)
  (error : Nat -> Real)
  (K : Nat -> Nat)
  (hhorizontal : forall n k, 0 <= horizontal n k)
  (hvertical : forall n k, 0 <= vertical n k)
  (herror0 : forall n, 0 <= error n)
  (herror : Tendsto error atTop (nhds 0))
  (hstart : forall n, horizontal n 0 <= vertical n 0 + error n)
  (hend : forall n, vertical n (K n + 1) <= horizontal n (K n + 1) + error n)
  (hlimits : forall k : Nat -> Nat, (forall n, k n < K n + 1) -> Tendsto (fun n => max (horizontal n (k n)) (vertical n (k n + 1))) atTop (nhds 1) /\ Tendsto (fun n => min (vertical n (k n)) (horizontal n (k n))) atTop (nhds 0) /\ Tendsto (fun n => min (vertical n (k n + 1)) (horizontal n (k n + 1))) atTop (nhds 0)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.approximate_balanced_height_sequence_contradiction horizontal vertical error K hhorizontal hvertical herror0 herror hstart hend hlimits


-- created on 2026-10-23
