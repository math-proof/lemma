module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.GHSDuplicateVariable.Part4
public import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
public import Theorem.StatisticalMechanics.Code.Inequalities.FKG
public import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part4
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


def ghsLSplitEquiv (q : ConfigSpace V) :
    ConfigSpace V ≃
      ((v : {v : V // q v = true}) → Bool) ×
        ((v : {v : V // ¬ q v = true}) → Bool) :=
  Equiv.piEquivPiSubtypeProd (fun v => q v = true) (fun _ => Bool)


end Ising
end StatMech
