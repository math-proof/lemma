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
public import Def.v1.Atlas.LieGroups.code.ChevalleyRestriction.Part4


public noncomputable section

open scoped TensorProduct

variable (R : Type*) [Field R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]

variable {R 𝔤}

attribute [instance] ChevalleyRestrictionData.instRing
  ChevalleyRestrictionData.instAlgebra

structure ChevalleyRestrictionPolyData
    {Δ : TriangularDecomposition R 𝔤} (wg : WeylGroupData Δ)
    (n m : ℕ) where
  G : Type*
  [instGroupG : Group G]


  G_action : G →* (MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R)
  W_action : wg.W →* (MvPolynomial (Fin m) R ≃ₐ[R] MvPolynomial (Fin m) R)
  Res : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin m) R
  Res_components : Fin n → MvPolynomial (Fin m) R
  Res_eq_aeval : Res = MvPolynomial.aeval Res_components
  Res_components_homogeneous : ∀ i, (Res_components i).IsHomogeneous 1
  Res_action_compat : ∀ (w : wg.W), ∃ (g : G),
    ∀ (p : MvPolynomial (Fin n) R),
      Res ((G_action g) p) = (W_action w) (Res p)
  kernel_trivial : ∀ (p : MvPolynomial (Fin n) R),
    p ∈ Subalgebra.invariants G G_action → Res p = 0 → p = 0


end
