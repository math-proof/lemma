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
import Def.v1.Atlas.LieGroups.code.ChevalleyRestriction.Part5


noncomputable section

open scoped TensorProduct

variable (R : Type*) [Field R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]

variable {R 𝔤}

attribute [instance] ChevalleyRestrictionData.instRing
  ChevalleyRestrictionData.instAlgebra

attribute [instance] ChevalleyRestrictionPolyData.instGroupG

omit [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤] in
theorem chevalley_restriction_polynomial
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {n m : ℕ}
    (cpd : ChevalleyRestrictionPolyData (R := R) (𝔤 := 𝔤) wg n m) :
    Function.Bijective cpd.restrictionMapPoly := by
  constructor
  ·
    intro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ heq

    have h_res : cpd.Res p₁ = cpd.Res p₂ := by
      have := congr_arg Subtype.val heq
      simpa [ChevalleyRestrictionPolyData.restrictionMapPoly, AlgHom.codRestrict] using this

    have hker : cpd.Res (p₁ - p₂) = 0 := by rw [map_sub, h_res, sub_self]

    have hinv : (p₁ - p₂) ∈ Subalgebra.invariants cpd.G cpd.G_action := by
      intro g; simp [map_sub, hp₁ g, hp₂ g]

    have h0 := cpd.kernel_trivial (p₁ - p₂) hinv hker

    exact Subtype.ext (eq_of_sub_eq_zero h0)
  ·
    intro ⟨q, hq⟩
    obtain ⟨p, hp_inv, hp_eq⟩ := cpd.Res_surjective' q hq

    exact ⟨⟨p, hp_inv⟩, Subtype.ext (by simpa [ChevalleyRestrictionPolyData.restrictionMapPoly, AlgHom.codRestrict] using hp_eq)⟩

end
