/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.Weights.Killing
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Theorem.v1.Atlas.LieGroups.code.ChevalleyRestriction.Part2

@[expose] public section

noncomputable section

open scoped TensorProduct

variable (R : Type*) [Field R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]

variable {R 𝔤}

attribute [instance] ChevalleyRestrictionData.instRing
  ChevalleyRestrictionData.instAlgebra

noncomputable def chevalleyRestrictionAlgEquiv
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ} :
    (chevalleyRestrictionData wg).adInvariant ≃ₐ[R] wg.invariantSubalgebra :=
  AlgEquiv.ofBijective (chevalleyRestrictionData wg).restrictionMap
    chevalley_restriction_bijective

end
