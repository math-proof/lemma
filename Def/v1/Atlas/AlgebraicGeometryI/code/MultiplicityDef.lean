/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MultiplicityDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
set_option maxHeartbeats 400000

open MvPolynomial


namespace MvPolynomial

variable {σ : Type*} {k : Type*} [CommRing k]

/-- Translate a polynomial by `p`, sending `X i` to `X i + C (p i)`. -/
noncomputable def translate (p : σ → k) (f : MvPolynomial σ k) : MvPolynomial σ k :=
  MvPolynomial.aeval (fun i => X i + C (p i)) f

/-- The minimum total degree among monomials appearing in `f` (Def 12). -/
noncomputable def minTotalDegree (f : MvPolynomial σ k) : ℕ := by
  classical
  exact if h : f.support.Nonempty then
    (f.support.image (fun s => Finsupp.sum s fun _ e => e)).min' (h.image _)
  else 0

/-- The multiplicity of `f` at the point `p` is the minimum total degree of the
translated polynomial `f(X + p)` (Def 12, 13). -/
noncomputable def multiplicityAt (f : MvPolynomial σ k) (p : σ → k) : ℕ :=
  (f.translate p).minTotalDegree

/-- Translation by `p` packaged as a `k`-algebra homomorphism. -/
noncomputable def translateAlgHom (p : σ → k) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun i => X i + C (p i))

end MvPolynomial
