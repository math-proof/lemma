/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_32_3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.CoradicalFiltration
import Lemma.Category.Atlas.v1.TensorCategories.code.CoradicalFiltration

set_option maxHeartbeats 800000

open scoped TensorProduct
open Coalgebra CategoryTheory MonoidalCategory

/-- The category of finite-dimensional right `H`-comodules, for `H` a Hopf algebra over `k`. -/
