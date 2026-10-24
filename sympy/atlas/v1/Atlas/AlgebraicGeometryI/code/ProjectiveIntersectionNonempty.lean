/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersectionNonempty.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.ProjectiveIntersection
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ProjectiveIntersection
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ProjectiveIntersectionBound
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.ProjectiveIntersectionBound
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field

noncomputable section
open Ideal
