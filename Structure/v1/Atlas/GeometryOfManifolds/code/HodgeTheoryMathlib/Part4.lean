/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheoryMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Interval
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib.Part5
set_option autoImplicit false


namespace HodgeMathlib

/-- A differential operator $L$ is elliptic if its principal symbol $\sigma(L)(\xi)$ is bijective for every nonzero covector $\xi$. -/
structure IsElliptic {n : ℕ}
    (L : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1))
    extends IsDifferentialOperator (n := n) L where
  elliptic : ∀ (ξ : Fin n → ℝ), ξ ≠ 0 →
    ∀ {k : ℕ}, Function.Bijective (principalSymbolDiffForm order coeff ξ (k := k))


/-- A smoothing operator: gains one Sobolev derivative, $\|S\,x\|_{s+1} \le C\,\|x\|_s$. -/
structure IsSmoothingOp {n k : ℕ}
    (sobolevNorm : ℕ → DiffForm n (k + 1) → ℝ)
    (S : DiffForm n (k + 1) →ₗ[ℝ] DiffForm n (k + 1)) where
  regularity_improvement : ∀ (s : ℕ), ∃ (C : ℝ), C > 0 ∧
    ∀ (x : DiffForm n (k + 1)), sobolevNorm (s + 1) (S x) ≤ C * sobolevNorm s x

/-- A parametrix for $L$: an operator $P$ with $PL = I + S_{\mathrm{left}}$ and $LP = I + S_{\mathrm{right}}$ modulo smoothing operators. -/
structure HasParametrix {n : ℕ}
    (L : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)) where
  P : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)
  S_left : ∀ {k : ℕ}, DiffForm n (k + 1) →ₗ[ℝ] DiffForm n (k + 1)
  S_right : ∀ {k : ℕ}, DiffForm n (k + 1) →ₗ[ℝ] DiffForm n (k + 1)
  sobolevNorm : ∀ {k : ℕ}, ℕ → DiffForm n (k + 1) → ℝ
  PL_eq : ∀ {k : ℕ} (α : DiffForm n (k + 1)), P (L α) = α + S_left α
  LP_eq : ∀ {k : ℕ} (α : DiffForm n (k + 1)), L (P α) = α + S_right α
  isSmoothing_S_left : ∀ {k : ℕ}, IsSmoothingOp (sobolevNorm (k := k)) (S_left (k := k))
  isSmoothing_S_right : ∀ {k : ℕ}, IsSmoothingOp (sobolevNorm (k := k)) (S_right (k := k))


end HodgeMathlib
