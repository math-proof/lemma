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
import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part17
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


def splitReorderEquiv (E : Type*) (m n : ℕ) :
    E × ((Fin m → E) × (Fin n → E)) ≃
      (Fin m → E) × (E × (Fin n → E)) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv x := by rcases x with ⟨s, l, r⟩; rfl
  right_inv x := by rcases x with ⟨l, s, r⟩; rfl


def splitPathEquiv (E : Type*) (m n : ℕ) :
    E × ((Fin m → E) × (Fin n → E)) ≃ (Fin (m + n + 1) → E) :=
  (splitReorderEquiv E m n).trans
    ((Equiv.refl (Fin m → E)).prodCongr (Fin.consEquiv fun _ : Fin (n + 1) => E)) |>.trans
      (Fin.appendEquiv m (n + 1)) |>.trans
        (Equiv.arrowCongr (finCongr (by omega)) (Equiv.refl E))

end StatMech.FrontierB
