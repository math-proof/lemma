/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec10SheafModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf

open AlgebraicGeometry

universe u

/-- Definition 25 (Lec 10): a sheaf of `O_X`-modules on a scheme `X`; abbreviation for
the mathlib `Scheme.Modules`. -/
abbrev SheafOfOXModules (X : Scheme.{u}) := X.Modules
