/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CenterMarkedPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.CylinderPathExpansion
import Theorem.StatisticalMechanics.Code.Ising.CenterMarkedPath
open Finset Matrix
open scoped BigOperators


namespace StatMech.Ising

def centerMarkedPathSum
    {E R : Type*} [Fintype E] [DecidableEq E] [CommSemiring R]
    (A : Matrix E E R) (a obs : E -> R) (n : Nat) : R :=
  ∑ q : Fin (2 * n + 1) -> E,
    a (q 0) * obs (q ⟨n, by omega⟩) *
      (∏ k : Fin (2 * n), A (q k.castSucc) (q k.succ)) *
      a (q (Fin.last (2 * n)))

end StatMech.Ising
