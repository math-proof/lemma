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


noncomputable section

open scoped TensorProduct

variable (R : Type*) [Field R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]

variable {R 𝔤}

structure ChevalleyRestrictionData (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ) where
  S𝔤 : Type*
  [instRing : Ring S𝔤]
  [instAlgebra : Algebra R S𝔤]
  adInvariant : Subalgebra R S𝔤
  restrictionAlgHom : S𝔤 →ₐ[R] UniversalEnvelopingAlgebra R Δ.𝔥
  algActionOnS𝔤 : wg.W →* (S𝔤 ≃ₐ[R] S𝔤)
  restriction_equivariant :
    ∀ (w : wg.W) (f : S𝔤),
      restrictionAlgHom ((algActionOnS𝔤 w) f) =
      (wg.algAction w) (restrictionAlgHom f)
  adInvariant_W_fixed :
    ∀ (w : wg.W) (f : S𝔤), f ∈ adInvariant →
      (algActionOnS𝔤 w) f = f
  eval𝔤 : S𝔤 → (𝔤 → R)
  eval𝔥 : UniversalEnvelopingAlgebra R Δ.𝔥 → (Δ.𝔥 → R)
  eval𝔤_injective : Function.Injective eval𝔤
  eval𝔥_injective : Function.Injective eval𝔥
  eval_restriction_compat : ∀ (f : S𝔤) (h : Δ.𝔥),
      eval𝔥 (restrictionAlgHom f) h = eval𝔤 f (h : 𝔤)
  adInvariant_eval_determined_by_h : ∀ (f₁ f₂ : S𝔤),
      f₁ ∈ adInvariant → f₂ ∈ adInvariant →
      (∀ h : Δ.𝔥, eval𝔤 f₁ (h : 𝔤) = eval𝔤 f₂ (h : 𝔤)) →
      ∀ x : 𝔤, eval𝔤 f₁ x = eval𝔤 f₂ x
  trace_function_surjectivity : ∀ (p : UniversalEnvelopingAlgebra R Δ.𝔥),
      p ∈ wg.invariantSubalgebra →
      ∃ f : S𝔤, f ∈ adInvariant ∧
        ∀ h : Δ.𝔥, eval𝔥 (restrictionAlgHom f) h = eval𝔥 p h

end
