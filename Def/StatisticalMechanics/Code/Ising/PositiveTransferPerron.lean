/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PositiveTransferPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open Finset Matrix Filter Topology


namespace StatMech.Ising

noncomputable section

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]

def coordinateAbs (v : EuclideanSpace Real alpha) :
    EuclideanSpace Real alpha :=
  WithLp.toLp 2 fun i => |v i|

end
end StatMech.Ising
