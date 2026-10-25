/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Torsors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.AddTorsor.Defs


/-- A `G`-torsor (principal homogeneous space) is a type `T` equipped with a free and transitive
action of the additive commutative group `G`. This is packaged as a `Mixin`-style class over
`AddTorsor G T`. -/
class IsTorsor (G : Type*) (T : Type*) [AddCommGroup G] extends AddTorsor G T


