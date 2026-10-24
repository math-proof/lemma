/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanCommutator.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.OrderRaising
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.OrderRaising
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators

open Finset

set_option autoImplicit false

namespace BooleanCommutator

variable {n : ℕ}

def DU_coeff (i : ℕ) (x z : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter (fun y : Finset (Fin n) =>
    y.card = i + 1 ∧ x ⊆ y ∧ z ⊆ y)).card

def UD_coeff (i : ℕ) (x z : Finset (Fin n)) : ℕ :=
  match i with
  | 0 => 0
  | i + 1 => (Finset.univ.filter (fun w : Finset (Fin n) =>
      w.card = i ∧ w ⊆ x ∧ w ⊆ z)).card
