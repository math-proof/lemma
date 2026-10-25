/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticManifoldMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.Dimension.Finrank
set_option autoImplicit false

open scoped TensorProduct


namespace SymplecticGeometry

/-- The wedge product $\omega \wedge \eta$ of two scalar-valued alternating forms,
producing an alternating $(m + k)$-form on $E$. -/
noncomputable def AlternatingMap.scalarWedge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m k : ℕ} (ω : E [⋀^Fin m]→ₗ[ℝ] ℝ) (η : E [⋀^Fin k]→ₗ[ℝ] ℝ) :
    E [⋀^Fin (m + k)]→ₗ[ℝ] ℝ :=
  ((TensorProduct.lid ℝ ℝ).toLinearMap.compAlternatingMap (ω.domCoprod η)).domDomCongr
    finSumFinEquiv

/-- The $n$-th wedge power $\omega^{\wedge n} = \underbrace{\omega \wedge \cdots \wedge \omega}_{n}$
of a $2$-form, yielding a $2n$-form. -/
noncomputable def AlternatingMap.wedgePower {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ω : E [⋀^Fin 2]→ₗ[ℝ] ℝ) : (n : ℕ) → E [⋀^Fin (2 * n)]→ₗ[ℝ] ℝ
  | 0 => AlternatingMap.constOfIsEmpty ℝ E (ι := Fin 0) 1
  | n + 1 => by
      have h : 2 * (n + 1) = 2 + 2 * n := by ring
      exact h ▸ AlternatingMap.scalarWedge ω (AlternatingMap.wedgePower ω n)


end SymplecticGeometry
