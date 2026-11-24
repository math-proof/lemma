module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma4.Part3
public import Theorem.StatisticalMechanics.Code.Onsager.ShermanSplit.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanReroot.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open Matrix BigOperators Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {n : ℕ} [NeZero n]


def ons_rotate (k : Fin n) (v : Fin n → E) : Fin n → E :=
  fun j => v (j + k)

end StatMech.Onsager
