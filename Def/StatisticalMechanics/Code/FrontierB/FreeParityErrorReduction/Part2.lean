/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeParityErrorReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.FreeMultipointEdwardsSokal.Part2
import Mathlib.Algebra.BigOperators.Ring.Nat
import Theorem.StatisticalMechanics.Code.FrontierB.FreeParityErrorReduction
open Set
open scoped BigOperators


namespace StatMech.FK

open StatMech.ConfigSpace

variable {V : Type*} (G : SimpleGraph V)

def TwoOddCrossClusters (omega : ConfigSpace (Sym2 V))
    (A B : Finset V) : Prop :=
  ∃ C₁ C₂ : (openSub G omega).ConnectedComponent,
    C₁ ≠ C₂ ∧
    Odd (clusterMarkCount G omega A C₁) ∧
    Odd (clusterMarkCount G omega B C₁) ∧
    Odd (clusterMarkCount G omega A C₂) ∧
    Odd (clusterMarkCount G omega B C₂)


end StatMech.FK
