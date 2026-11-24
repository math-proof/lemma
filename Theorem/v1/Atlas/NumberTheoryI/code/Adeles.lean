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
public import Instance.v1.Atlas.NumberTheoryI.code.Adeles


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

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem adicCompletion_finite_residueField
    (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    Empty.Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  haveI : Empty.Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  exact Empty.Finite.of_equiv (𝓞 K ⧸ v.asIdeal)
    (KroneckerWeber.completion_residueFieldEquiv (𝓞 K) K v).symm.toEquiv

end NumberField.Adeles
end
