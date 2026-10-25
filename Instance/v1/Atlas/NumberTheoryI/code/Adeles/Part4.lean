/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
import Abbrev.v1.Atlas.NumberTheoryI.code.Adeles.Part2


noncomputable section

open NumberField IsDedekindDomain

open scoped TensorProduct

namespace NumberField.Adeles

variable {K : Type*} [Field K] [NumberField K]

section RestrictedProductDirectLimit

open Filter Set Topology

instance infinitePlace_properSpace (v : InfinitePlace K) :
    ProperSpace v.Completion := by
  open InfinitePlace.Completion in
  constructor
  intro x r
  rcases v.isReal_or_isComplex with hv | hv
  · have e := isometryEquivRealOfIsReal hv
    rw [show Metric.closedBall x r = e.symm '' (Metric.closedBall (e x) r) from ?_]
    · exact (isCompact_closedBall (e x) r).image e.symm.continuous
    · ext y; simp only [Set.mem_image, Metric.mem_closedBall]
      exact ⟨fun h => ⟨e y, by rwa [e.dist_eq], by simp⟩,
             fun ⟨z, hz, hzy⟩ => by rw [← hzy, ← e.dist_eq]; simpa using hz⟩
  · have e := isometryEquivComplexOfIsComplex hv
    rw [show Metric.closedBall x r = e.symm '' (Metric.closedBall (e x) r) from ?_]
    · exact (isCompact_closedBall (e x) r).image e.symm.continuous
    · ext y; simp only [Set.mem_image, Metric.mem_closedBall]
      exact ⟨fun h => ⟨e y, by rwa [e.dist_eq], by simp⟩,
             fun ⟨z, hz, hzy⟩ => by rw [← hzy, ← e.dist_eq]; simpa using hz⟩

end RestrictedProductDirectLimit
end NumberField.Adeles
end
