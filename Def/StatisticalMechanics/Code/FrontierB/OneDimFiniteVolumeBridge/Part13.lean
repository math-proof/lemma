/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.OneDimTransferPerron
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part12
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


def centerReorderEquiv (E : Type*) (n : ℕ) :
    E × ((Fin n → E) × (Fin n → E)) ≃
      (Fin n → E) × (E × (Fin n → E)) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv x := by rcases x with ⟨s,l,r⟩; rfl
  right_inv x := by rcases x with ⟨l,s,r⟩; rfl

def centerPathEquiv (E : Type*) (n : ℕ) :
    E × ((Fin n → E) × (Fin n → E)) ≃ (Fin (2 * n + 1) → E) :=
  (centerReorderEquiv E n).trans
    ((Equiv.refl (Fin n → E)).prodCongr (Fin.consEquiv fun _ : Fin (n + 1) => E)) |>.trans
      (Fin.appendEquiv n (n + 1)) |>.trans
        (Equiv.arrowCongr (finCongr (by omega)) (Equiv.refl E))

end StatMech.FrontierB
