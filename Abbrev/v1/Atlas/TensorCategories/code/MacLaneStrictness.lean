/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MacLaneStrictness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.End
public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.Free.Coherence
public import Mathlib.CategoryTheory.Monoidal.Free.Basic
public import Instance.v1.Atlas.TensorCategories.code.MacLaneStrictness
@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category


namespace EGNO.MacLaneStrictness

section SkeletalStrictness

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A skeletal monoidal category yields a monoid structure on the type of its objects. -/
noncomputable abbrev skeletal_monoidFromMonoidal (hC : Skeletal C) : Monoid C :=
  monoidOfSkeletalMonoidal hC

end SkeletalStrictness
end EGNO.MacLaneStrictness
