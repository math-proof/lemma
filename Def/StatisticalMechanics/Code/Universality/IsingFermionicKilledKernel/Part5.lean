/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part4


namespace StatMech.Universality

open Finset

noncomputable section

noncomputable def isingLineBinomialKernel (t : Nat) (x y : Int) : Real :=
  ∑ k ∈ range (t + 1),
    if y = x + 2 * (k : Int) - (t : Int) then
      isingBinomialWeight t k
    else 0

end
end StatMech.Universality
