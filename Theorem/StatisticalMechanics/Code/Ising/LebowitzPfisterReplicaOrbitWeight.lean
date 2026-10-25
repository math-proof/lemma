/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitWeight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRepresentatives.Part3
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitWeight
open Finset


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplica_factorialPower_pair (X : Real) (a b : Nat) :
    X ^ a / Nat.factorial a * (X ^ b / Nat.factorial b) =
      X ^ (a + b) / Nat.factorial (a + b) *
        (Nat.choose (a + b) a : Real) := by
  have hnat : (a + b).choose a *
      (Nat.factorial a * Nat.factorial b) =
      Nat.factorial (a + b) := by
    have h := Nat.add_choose_mul_factorial_mul_factorial b a
    rw [Nat.add_comm b a] at h
    rw [<- h]
    ring
  have hfac : ((a + b).choose a : Real) *
      (Nat.factorial a * Nat.factorial b) =
      Nat.factorial (a + b) := by
    exact_mod_cast hnat
  have haf : (Nat.factorial a : Real) ≠ 0 := by
    exact_mod_cast a.factorial_ne_zero
  have hbf : (Nat.factorial b : Real) ≠ 0 := by
    exact_mod_cast b.factorial_ne_zero
  have habf : (Nat.factorial (a + b) : Real) ≠ 0 := by
    exact_mod_cast (a + b).factorial_ne_zero
  rw [pow_add]
  field_simp
  rw [<- hfac]
  ring


end
end StatMech.Ising
