/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
import Lemma.Int.Any_All_Eq.of.LeKer_Ker.Surjective
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Theorem.v1.Atlas.LieGroups.code.ChevalleyRestriction.Part4


noncomputable section

open scoped TensorProduct

variable (R : Type*) [Field R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]

variable {R 𝔤}

attribute [instance] ChevalleyRestrictionData.instRing
  ChevalleyRestrictionData.instAlgebra

attribute [instance] ChevalleyRestrictionPolyData.instGroupG

noncomputable def chevalleyRestrictionTheorem_10_1_algEquiv
    {k : Type*} [Field k]
    {𝔤₀ : Type*} [LieRing 𝔤₀] [LieAlgebra k 𝔤₀]
    [LieAlgebra.IsKilling k 𝔤₀] [FiniteDimensional k 𝔤₀]
    {Δ : TriangularDecomposition k 𝔤₀} {wg : WeylGroupData Δ}
    {n m : ℕ}
    (cpd : ChevalleyRestrictionPolyData (R := k) (𝔤 := 𝔤₀) wg n m) :
    Subalgebra.invariants cpd.G cpd.G_action ≃ₐ[k]
    Subalgebra.invariants wg.W cpd.W_action :=
  AlgEquiv.ofBijective _ (chevalley_restriction_theorem_10_1 cpd)

noncomputable def chevalley_restriction_isomorphism
    {k : Type*} [Field k]
    {𝔤₀ : Type*} [LieRing 𝔤₀] [LieAlgebra k 𝔤₀]
    [LieAlgebra.IsKilling k 𝔤₀] [FiniteDimensional k 𝔤₀]
    {Δ : TriangularDecomposition k 𝔤₀} {wg : WeylGroupData Δ}
    {n m : ℕ}
    (cpd : ChevalleyRestrictionPolyData (R := k) (𝔤 := 𝔤₀) wg n m) :
    Subalgebra.invariants cpd.G cpd.G_action ≃ₐ[k]
    Subalgebra.invariants wg.W cpd.W_action :=
  chevalleyRestrictionTheorem_10_1_algEquiv cpd

end
