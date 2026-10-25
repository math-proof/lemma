/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PositiveTransferPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PositiveTransferPerron
open Finset Matrix Filter Topology


namespace StatMech.Ising

noncomputable section

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]

def positiveTransferTopIndex : Fin (Fintype.card alpha) :=
  ⟨0, Fintype.card_pos⟩


def positiveTransferTopEigenvalue (A : Matrix alpha alpha Real)
    (hA : A.IsHermitian) : Real :=
  hA.eigenvalues₀ (positiveTransferTopIndex (alpha := alpha))

end
end StatMech.Ising
