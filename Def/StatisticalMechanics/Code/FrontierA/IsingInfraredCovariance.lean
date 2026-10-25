/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredCovariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredReduction
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
open Finset
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

variable {Gamma Omega : Type*}

variable [Fintype Gamma] [AddCommGroup Gamma]


def HasFiniteStationaryGramRepresentation
    [Fintype Omega]
    (G : Gamma → ℝ) (weight : Omega → ℝ)
    (field : Omega → Gamma → ℝ) : Prop :=
  (∀ omega, 0 ≤ weight omega) ∧
    forall x z, G z =
      ∑ omega,
        weight omega * field omega x * field omega (x + z)

end StatMech.FrontierA
