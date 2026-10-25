/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ideles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.GroupTheory.FiniteIndexNormalSubgroup
import Def.v1.Atlas.NumberTheoryI.code.Adeles.Part10
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Adeles
import Abbrev.v1.Atlas.NumberTheoryI.code.Ideles.Part3


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
