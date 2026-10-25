/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/BlockMatrixLp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false


/-- Algebraic data packaging a 2×2 block-matrix symplectic form on $V \oplus W$:
an evaluation pairing $\mathrm{eval} : W \otimes V \to \mathbb{R}$, an invertible
block endomorphism $B$ on $V$ together with its transpose-inverse $B^{-T}$ on $W$,
and a skew form $C$ on $W$ realized via $\tilde C : W \to V$. -/
structure BlockSymplecticData (V W : Type*)
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] where
  eval : W →ₗ[ℝ] V →ₗ[ℝ] ℝ
  B_endo : V →ₗ[ℝ] V
  B_inv : V →ₗ[ℝ] V
  hBinv_left : ∀ v, B_inv (B_endo v) = v
  hBinv_right : ∀ v, B_endo (B_inv v) = v
  B_inv_t : W →ₗ[ℝ] W
  hBinvt : ∀ w v, eval (B_inv_t w) v = eval w (B_inv v)
  C_form : W →ₗ[ℝ] W →ₗ[ℝ] ℝ
  hC_skew : ∀ w₁ w₂, C_form w₁ w₂ = -(C_form w₂ w₁)
  C_tilde : W →ₗ[ℝ] V
  hCtilde : ∀ w₁ w₂, eval w₁ (C_tilde w₂) = C_form w₁ w₂

