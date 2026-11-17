/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityNonneg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
public import Theorem.StatisticalMechanics.Code.SLE.CapacityProps

@[expose] public section

open scoped UpperHalfPlane NNReal
open Filter Topology Complex Bornology


namespace StatMech.SLE

def ShrinksIm (g : ℂ → ℂ) : Prop := ∀ z : ℂ, 0 < z.im → (g z).im ≤ z.im


end StatMech.SLE
