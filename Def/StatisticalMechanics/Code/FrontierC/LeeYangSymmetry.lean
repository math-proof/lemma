/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.LeeYangPolynomial
import Mathlib.Algebra.Polynomial.Reverse
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierC

open StatMech.Ising StatMech.FrontierB

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def leeYangFlip (s : ConfigSpace V) : ConfigSpace V := fun x => !(s x)

end StatMech.FrontierC
