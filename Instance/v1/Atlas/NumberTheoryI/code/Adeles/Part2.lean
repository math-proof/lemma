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
public import Theorem.v1.Atlas.NumberTheoryI.code.Adeles


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

noncomputable instance adicCompletion_compactSpace_integer
    (v : HeightOneSpectrum (𝓞 K)) :
    CompactSpace (Valued.integer (v.adicCompletion K)) := by
  letI := Valued.toNontriviallyNormedField (v.adicCompletion K) (WithZero (Multiplicative ℤ))
  rw [Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
  exact ⟨(Valued.isClosed_integer _).completeSpace_coe,
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K)),
    adicCompletion_finite_residueField K v⟩

noncomputable instance adicCompletion_properSpace
    (v : HeightOneSpectrum (𝓞 K)) :
    ProperSpace (v.adicCompletion K) := by
  letI := Valued.toNontriviallyNormedField (v.adicCompletion K) (WithZero (Multiplicative ℤ))
  exact Valued.integer.properSpace_iff_compactSpace_integer.mpr
    (adicCompletion_compactSpace_integer v)

end NumberField.Adeles
end
