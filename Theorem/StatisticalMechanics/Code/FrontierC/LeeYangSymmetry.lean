/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.LeeYangPolynomial
import Mathlib.Algebra.Polynomial.Reverse
import Def.StatisticalMechanics.Code.FrontierC.LeeYangSymmetry
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierC

open StatMech.Ising StatMech.FrontierB

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


omit [Fintype V] [DecidableEq V] in
@[simp] theorem leeYangFlip_apply (s : ConfigSpace V) (x : V) :
    leeYangFlip s x = !(s x) := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem leeYangFlip_involutive (s : ConfigSpace V) :
    leeYangFlip (leeYangFlip s) = s := by
  funext x
  simp [leeYangFlip]


end StatMech.FrontierC
