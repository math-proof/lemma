/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec22GenericSmoothness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Order


noncomputable section

namespace Lec22

open MvPolynomial

/-- The number of monomials of degree `d` in `n + 1` variables, equal to `choose (n + d) d`. -/
def veroneseMonomialCount (n d : ℕ) : ℕ := Nat.choose (n + d) d

/-- The dimension `N` of the projective target of the degree-`d` Veronese embedding
of `ℙⁿ`, equal to `choose (n + d) d - 1`. -/
def veroneseTargetDim (n d : ℕ) : ℕ := veroneseMonomialCount n d - 1

/-- Smoothness of the projective hypersurface `V(f) ⊆ ℙⁿ`: at every nonzero point where
`f` vanishes, some partial derivative of `f` is nonzero (Jacobian criterion). -/
def IsSmooth_Hypersurface (k : Type*) [CommRing k] (n : ℕ)
    (f : MvPolynomial (Fin (n + 1)) k) : Prop :=
  ∀ x : Fin (n + 1) → k,
    (∃ i, x i ≠ 0) →
    MvPolynomial.eval x f = 0 →
    ∃ i : Fin (n + 1), MvPolynomial.eval x (MvPolynomial.pderiv i f) ≠ 0

end Lec22
end
