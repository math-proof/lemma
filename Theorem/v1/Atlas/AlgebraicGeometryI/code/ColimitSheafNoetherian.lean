/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ColimitSheafNoetherian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.NoetherianSpace
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Filtered.Basic
universe w v u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

/-- Lemma 22 (Lec 6/12): on a Noetherian topological space, the colimit of a filtered diagram of
sheaves, taken in the presheaf category, is itself a sheaf. -/


