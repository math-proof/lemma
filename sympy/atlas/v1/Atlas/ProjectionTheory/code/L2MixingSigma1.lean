/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/L2MixingSigma1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.ProjectionTheory.code.SelbergExpansion
import Lemma.Real.Atlas.v1.ProjectionTheory.code.SelbergExpansion

open Matrix Finset BigOperators

noncomputable section

namespace SelbergExpansion

section L2Mixing

variable {G : Type*} [Fintype G] [DecidableEq G] [Group G]
