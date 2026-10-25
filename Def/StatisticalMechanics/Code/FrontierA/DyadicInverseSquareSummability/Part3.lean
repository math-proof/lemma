/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/DyadicInverseSquareSummability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Theorem.StatisticalMechanics.Code.FrontierA.DyadicInverseSquareSummability.Part3
open Filter Finset Set Topology


namespace StatMech.FrontierA

noncomputable section

def dyadicUpperEquiv {Q : Type*} (size : Q → Real) :
    (Σ n : Nat, DyadicUpperFiber size n) ≃ Q where
  toFun q := q.2.1
  invFun q := ⟨dyadicUpperLevel size q, ⟨q, rfl⟩⟩
  left_inv q := by
    rcases q with ⟨n, q, hq⟩
    cases hq
    rfl
  right_inv q := rfl

end
end StatMech.FrontierA
