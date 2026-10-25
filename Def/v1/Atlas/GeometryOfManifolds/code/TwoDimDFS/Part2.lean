/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/TwoDimDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Instance.v1.Atlas.GeometryOfManifolds.code.TwoDimDFS
set_option autoImplicit false
set_option maxHeartbeats 800000


noncomputable section

/-- Exterior derivative on polynomial forms on $\mathbb{R}^2$: $df = (\partial_x f, \partial_y f)$
on $0$-forms, $d(f\,dx + g\,dy) = \partial_x g - \partial_y f$ on $1$-forms, and $0$ in higher degree. -/
noncomputable def symp2d : ∀ {p : ℕ}, Symp2Ω p → Symp2Ω (p + 1)
  | 0, f => (MvPolynomial.pderiv (0 : Fin 2) f, MvPolynomial.pderiv (1 : Fin 2) f)
  | 1, (f, g) => MvPolynomial.pderiv (0 : Fin 2) g - MvPolynomial.pderiv (1 : Fin 2) f
  | 2, _ => PUnit.unit
  | _ + 3, _ => PUnit.unit

/-- Interior product $\iota_X$ on polynomial forms on $\mathbb{R}^2$ with $X = (a, b)$:
on $1$-forms $\iota_X(f, g) = af + bg$, on $2$-forms $\iota_X h = (-hb, ha)$, and $0$ in higher degree. -/
noncomputable def symp2Iota : Symp2VF → ∀ {p : ℕ}, Symp2Ω (p + 1) → Symp2Ω p
  | (a, b), 0, (f, g) => a * f + b * g
  | (a, b), 1, h => (-h * b, h * a)
  | _, 2, _ => (0 : Poly2)
  | _, (_ + 3), _ => PUnit.unit

/-- Scaling a polynomial $p$-form on $\mathbb{R}^2$ by a polynomial $0$-form, defined componentwise. -/
noncomputable def symp2fMul : ∀ {p : ℕ}, Symp2Ω 0 → Symp2Ω p → Symp2Ω p
  | 0, f, α => f * α
  | 1, f, (a, b) => (f * a, f * b)
  | 2, f, h => f * h
  | _ + 3, _, _ => PUnit.unit

/-- Wedge product of a polynomial $1$-form with a polynomial $p$-form on $\mathbb{R}^2$,
yielding a $(p+1)$-form; nontrivial only for $p = 0$ and $p = 1$. -/
noncomputable def symp2wedge1 : ∀ {p : ℕ}, Symp2Ω 1 → Symp2Ω p → Symp2Ω (p + 1)
  | 0, (f, g), α => (f * α, g * α)
  | 1, (f₁, g₁), (f₂, g₂) => f₁ * g₂ - g₁ * f₂
  | 2, _, _ => PUnit.unit
  | _ + 3, _, _ => PUnit.unit

/-- Lie derivative $\mathcal{L}_X$ on polynomial forms on $\mathbb{R}^2$, defined via Cartan's
magic formula $\mathcal{L}_X = d \circ \iota_X + \iota_X \circ d$. -/
noncomputable def symp2L : Symp2VF → ∀ {p : ℕ}, Symp2Ω p → Symp2Ω p
  | X, 0, f => symp2Iota X (symp2d f)
  | X, 1, α => symp2d (symp2Iota X α) + symp2Iota X (symp2d α)
  | X, 2, h => symp2d (symp2Iota X h) + symp2Iota X (symp2d h)
  | _, _ + 3, _ => PUnit.unit


end
