/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.LeeYangPolynomial
import Mathlib.Algebra.Polynomial.Reverse
import Theorem.StatisticalMechanics.Code.FrontierC.LeeYangSymmetry
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierC

open StatMech.Ising StatMech.FrontierB

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def leeYangFlipEquiv : ConfigSpace V ≃ ConfigSpace V where
  toFun := leeYangFlip
  invFun := leeYangFlip
  left_inv := leeYangFlip_involutive
  right_inv := leeYangFlip_involutive

end StatMech.FrontierC
