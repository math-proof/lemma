/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open nonZeroDivisors


noncomputable abbrev principalFractionalIdeal (x : K) : FractionalIdeal A⁰ K :=
  FractionalIdeal.spanSingleton A⁰ x

