/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Rings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Rings

example : CommRing ℤ := inferInstance

example : CommRing ℚ := inferInstance

example : CommRing ℝ := inferInstance

example : CommRing ℂ := inferInstance

example (n : ℕ) : CommRing (ZMod n) := inferInstance
