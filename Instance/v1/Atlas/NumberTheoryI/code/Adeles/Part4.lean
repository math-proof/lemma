module
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.Topology.Algebra.Group.Compact
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Free
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
public import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
public import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
public import Abbrev.v1.Atlas.NumberTheoryI.code.Adeles.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
