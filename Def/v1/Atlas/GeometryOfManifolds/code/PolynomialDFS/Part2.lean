/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/PolynomialDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Instance.v1.Atlas.GeometryOfManifolds.code.PolynomialDFS
set_option autoImplicit false


/-- Multiplication of a polynomial $0$-form (function) by a $p$-form: pointwise polynomial product. -/
noncomputable def polyFMul : {p : ℕ} → PolyΩ 0 → PolyΩ p → PolyΩ p
  | 0, f, α => f * α
  | 1, f, α => f * α
  | _ + 2, _, _ => PUnit.unit

/-- Wedge of a $1$-form with a $p$-form on $\mathbb{R}$: nontrivial only when $p = 0$. -/
noncomputable def polyWedge1 : {p : ℕ} → PolyΩ 1 → PolyΩ p → PolyΩ (p + 1)
  | 0, ω, α => ω * α
  | _ + 1, _, _ => PUnit.unit

/-- Exterior derivative on polynomial forms: $d f = f'\, dt$ for a $0$-form, zero in higher degree. -/
noncomputable def polyD : {p : ℕ} → PolyΩ p → PolyΩ (p + 1)
  | 0, f => Polynomial.derivative f
  | _ + 1, _ => PUnit.unit

/-- Interior product (contraction) $\iota_X$ of a vector field $X$ with a polynomial form. -/
noncomputable def polyIota (X : PolyVF) : {p : ℕ} → PolyΩ (p + 1) → PolyΩ p
  | 0, α => X * α
  | 1, _ => (0 : Polynomial ℝ)
  | _ + 2, _ => PUnit.unit

/-- Lie derivative $\mathcal{L}_X$ on polynomial forms, via Cartan's magic formula
$\mathcal{L}_X = d \circ \iota_X + \iota_X \circ d$. -/
noncomputable def polyLie (X : PolyVF) : {p : ℕ} → PolyΩ p → PolyΩ p
  | 0, f => X * Polynomial.derivative f
  | 1, g => Polynomial.derivative (X * g)
  | _ + 2, _ => PUnit.unit

/-- Formal antiderivative of a real polynomial: $\int (\sum a_n t^n)\, dt = \sum \tfrac{a_n}{n+1} t^{n+1}$. -/
noncomputable def polyAntideriv (g : Polynomial ℝ) : Polynomial ℝ :=
  g.sum (fun n a => Polynomial.monomial (n + 1) (a / (↑(n + 1) : ℝ)))

