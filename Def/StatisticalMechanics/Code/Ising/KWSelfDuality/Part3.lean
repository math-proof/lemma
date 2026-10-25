/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWSelfDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Theorem.StatisticalMechanics.Code.Ising.KWSelfDuality.Part3
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

section SelfDual

open Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp Gd : SimpleGraph V) [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


def DualContourMatching (β βstar c : ℝ) : Prop :=
  Real.tanh βstar = Real.exp (-2 * β) ∧
    (2 : ℝ) ^ Fintype.card V * (Real.cosh βstar) ^ Gd.edgeFinset.card
        * ∑ F ∈ Gd.edgeFinset.powerset.filter IsEvenSubgraph,
            (Real.tanh βstar) ^ F.card
      = c * isingZ Gp β 0


end SelfDual
end Ising
end StatMech
