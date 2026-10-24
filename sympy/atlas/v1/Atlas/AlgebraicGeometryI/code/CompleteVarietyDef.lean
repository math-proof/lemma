/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CompleteVarietyDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Over

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Definition 19 (Lec 8): a scheme `X` over `S` is *complete* if its structural morphism is
proper (i.e. separated, universally closed, and locally of finite type). -/
def IsComplete (X S : Scheme.{u}) [X.Over S] : Prop :=
  IsProper (X ↘ S)
