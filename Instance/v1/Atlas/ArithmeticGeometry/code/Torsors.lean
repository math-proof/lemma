/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Torsors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.AddTorsor.Defs
import Class.v1.Atlas.ArithmeticGeometry.code.Torsors


/-- Every additive commutative group `G` is a torsor over itself, with action given by addition. -/
instance IsTorsor.self (G : Type*) [AddCommGroup G] : IsTorsor G G := ⟨⟩


