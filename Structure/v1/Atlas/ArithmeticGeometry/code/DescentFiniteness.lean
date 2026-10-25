/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/DescentFiniteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


/-- Abstract descent data: an abelian group $A$, a subgroup $\mathrm{im}(\varphi) \subseteq A$, a non-zero integer $B$ controlling the descent, and a "descent representative" $A \to \mathbb{Z}$. -/
structure DescentData where
  B : ℤ
  hB : B ≠ 0
  carrier : Type
  [instAddCommGroup : AddCommGroup carrier]
  imageOfPhi : AddSubgroup carrier
  descentRepr : carrier → ℤ

