module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ideles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.Topology.Algebra.Group.Compact
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.GroupTheory.FiniteIndexNormalSubgroup
public import Def.v1.Atlas.NumberTheoryI.code.Adeles.Part10
public import Abbrev.v1.Atlas.NumberTheoryI.code.Ideles.Part3
public section

noncomputable section

open NumberField IsDedekindDomain

namespace Ideles

section ProfiniteGroups

open CategoryTheory in
class IsProfiniteGroup (G : Type*) [Group G] [TopologicalSpace G] : Prop where
  isInverseLimitOfFiniteGroups :
    ∃ (J : Type) (_ : SmallCategory J) (F : Functor J FiniteGrp.{0}),
      Nonempty (G ≃ₜ* ProfiniteGrp.limit (F ⋙ forget₂ FiniteGrp ProfiniteGrp))

end ProfiniteGroups
end Ideles
end
