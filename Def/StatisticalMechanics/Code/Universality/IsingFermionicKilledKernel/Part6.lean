/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part5


namespace StatMech.Universality

open Finset

noncomputable section

noncomputable def isingLeapfrogFreeBinomialKernel
    (t : Nat) (p q : IsingLeapfrogPlane) : Real :=
  isingLineBinomialKernel t p.1 q.1 *
    isingLineBinomialKernel t p.2 q.2

end
end StatMech.Universality
