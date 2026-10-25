/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PolygonWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.PolygonWalk


namespace StatMech.Onsager.PolygonWalk

def cornerBalance {n : ℕ} (t : Fin n → ℤ) : ℤ := ∑ i, t i


end StatMech.Onsager.PolygonWalk
