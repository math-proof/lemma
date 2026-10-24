/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffineVarietyCharacterization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.FiniteType
import Mathlib.CategoryTheory.Iso
import Mathlib.FieldTheory.IsAlgClosed.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec2AffineVarieties
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.Lec2AffineVarieties

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u
