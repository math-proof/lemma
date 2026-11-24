module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.GHSDuplicateVariable.Part4
public import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
public import Theorem.StatisticalMechanics.Code.Inequalities.FKG
public import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part10
open scoped BigOperators symmDiff
open Finset SimpleGraph Set
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def GHSLebowitzFibreFactorization (β h : ℝ) (o x y : V) : Prop :=
  ∀ q : ConfigSpace V,
    ghsLFibreExpectation G β h
        (fun a b => uvar a b o * uvar a b x * tvar a b y) q
      = ghsLFibreUU G β h o x q * ghsLFibreT G β h y q


end Ising
end StatMech
