/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusLaplacianNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGraph.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusExponentialMoment
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
open Finset Matrix
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


theorem isingTorusGraph_reachable_add_nsmul_step
    (x : IsingDyadicTorus d k) (i : Fin d) (n : Nat) :
    (isingTorusGraph d k).Reachable x
      (x + n • isingTorusStep i) := by
  induction n with
  | zero => simp
  | succ n hn =>
      have hadj : (isingTorusGraph d k).Adj
          (x + n • isingTorusStep i)
          ((x + n • isingTorusStep i) + isingTorusStep i) :=
        ⟨i, Or.inl rfl⟩
      convert hn.trans hadj.reachable using 1
      ext j
      simp only [Pi.add_apply, nsmul_eq_mul,
        Nat.cast_succ, Pi.mul_apply, Pi.one_apply]
      ring


theorem isingTorusGraph_connected :
    (isingTorusGraph d k).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun y => ?_⟩
  have hsum (S : Finset (Fin d)) :
      (isingTorusGraph d k).Reachable 0
        (∑ i ∈ S, Pi.single i (y i)) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
        let x : IsingDyadicTorus d k := ∑ j ∈ S, Pi.single j (y j)
        have hcoord :
            (y i).val • (isingTorusStep i : IsingDyadicTorus d k) =
              Pi.single i (y i) := by
          ext j
          by_cases hji : j = i
          · subst j
            simp [isingTorusStep]
          · simp [isingTorusStep, Pi.single_eq_of_ne hji]
        have hstep := isingTorusGraph_reachable_add_nsmul_step
          (d := d) (k := k) x i (y i).val
        rw [hcoord] at hstep
        simpa [x, hi, add_comm] using ih.trans hstep
  simpa [Finset.univ_sum_single] using hsum Finset.univ


end StatMech.FrontierA
