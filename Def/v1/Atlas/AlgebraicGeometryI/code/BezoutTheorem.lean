/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.AlgebraTower
import Mathlib.Algebra.Polynomial.Monic
set_option maxHeartbeats 400000

open Polynomial


/-- Algebra isomorphism relating the bivariate quotient `k[X][Y] / ⟨C(X² + 1), Y⟩` to the
univariate quotient `k[X] / ⟨X² + 1⟩`, used to compute the line/conic intersection dimension. -/
noncomputable def lineConicQuotientEquiv (k : Type*) [Field k] :
    (Polynomial (Polynomial k) ⧸ Ideal.span
      {Polynomial.C ((X : Polynomial k)^2 + 1), (X : Polynomial (Polynomial k))})
      ≃ₐ[Polynomial k]
    (Polynomial k ⧸ Ideal.span {(X : Polynomial k)^2 + 1}) := by
  have h : (Ideal.span {Polynomial.C ((X : Polynomial k)^2 + 1),
      (X : Polynomial (Polynomial k))} : Ideal (Polynomial (Polynomial k))) =
    Ideal.span {Polynomial.C ((X : Polynomial k)^2 + 1),
      (X : Polynomial (Polynomial k)) - C 0} := by simp
  exact (Ideal.quotientEquivAlgOfEq (Polynomial k) h).trans
    (quotientSpanCXSubCAlgEquiv ((X : Polynomial k)^2 + 1) (0 : Polynomial k))

/-- Chinese remainder theorem for coprime polynomials: `k[X] / ⟨f g⟩ ≅ k[X]/⟨f⟩ × k[X]/⟨g⟩`. -/
noncomputable def coprime_polynomial_CRT (k : Type*) [Field k]
    (f g : Polynomial k) (hfg : IsCoprime f g) :
    (Polynomial k ⧸ Ideal.span {f * g}) ≃+*
    (Polynomial k ⧸ Ideal.span {f}) × (Polynomial k ⧸ Ideal.span {g}) := by
  have hsup : Ideal.span {f} ⊔ Ideal.span {g} = ⊤ :=
    (Ideal.sup_eq_top_iff_isCoprime f g).mpr hfg
  have hinf : Ideal.span {f * g} = Ideal.span {f} ⊓ Ideal.span {g} := by
    rw [← Ideal.span_singleton_mul_span_singleton,
        Ideal.mul_eq_inf_of_coprime hsup]
  exact (Ideal.quotEquivOfEq hinf).trans
    (Ideal.quotientInfEquivQuotientProd _ _
      (Ideal.isCoprime_iff_sup_eq.mpr hsup))

/-- The canonical power basis `1, X, X², …, X^{deg g - 1}` of `R[X] / ⟨g⟩` over `R` when `g`
is monic. -/
noncomputable def quotient_polynomial_powerBasis (R : Type*) [CommRing R]
    (g : Polynomial R) (hg : g.Monic) :
    PowerBasis R (AdjoinRoot g) :=
  AdjoinRoot.powerBasis' hg

/-- Algebra isomorphism `k[X][Y] / (⟨g⟩ + ⟨f⟩) ≅ AdjoinRoot g / ⟨[f]⟩` obtained via the
quotient-of-quotients construction. -/
noncomputable def bivariate_quotient_equiv (k : Type*) [Field k]
    (f g : Polynomial (Polynomial k)) :
    (Polynomial (Polynomial k) ⧸ (Ideal.span {g} ⊔ Ideal.span {f})) ≃ₐ[k]
    (AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.mk g f}) := by
  have h : Ideal.map (Ideal.Quotient.mkₐ k (Ideal.span {g})) (Ideal.span {f}) =
      Ideal.span {AdjoinRoot.mk g f} := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  exact (DoubleQuot.quotQuotEquivQuotSupₐ k (Ideal.span {g}) (Ideal.span {f})).symm.trans
    (Ideal.quotientEquivAlgOfEq k h)

