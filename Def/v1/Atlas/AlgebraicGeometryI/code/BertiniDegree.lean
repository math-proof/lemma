/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Length
import Mathlib.Algebra.Exact
import Mathlib.RingTheory.MvPolynomial.EulerIdentity


noncomputable section

open MvPolynomial Finset

section Bertini

/-- A point `x` is a *singular zero* of `f` if `f(x) = 0` and all partial derivatives vanish at
`x`. These are the singular points of the hypersurface `V(f)`. -/
def IsSingularZero {k : Type*} [CommRing k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k) (x : Fin (n + 1) → k) : Prop :=
  MvPolynomial.eval x f = 0 ∧
    ∀ i : Fin (n + 1), MvPolynomial.eval x (pderiv i f) = 0

/-- The *Fermat polynomial* of degree `d` in `n+1` variables: `x₀^d + x₁^d + … + xₙ^d`. -/
def fermatPoly (k : Type*) [CommSemiring k] (n d : ℕ) :
    MvPolynomial (Fin (n + 1)) k :=
  ∑ i : Fin (n + 1), X i ^ d

/-- The *discriminant locus*: the set of degree-`d` homogeneous polynomials whose hypersurface
has a singular point. -/
def discriminantLocus (k : Type*) [Field k] (n d : ℕ) :
    Set (MvPolynomial (Fin (n + 1)) k) :=
  {f | f.IsHomogeneous d ∧ ∃ x : Fin (n + 1) → k, x ≠ 0 ∧ IsSingularZero f x}

/-- Two `R`-modules are *equivalent* in `K₀` (with the length map) if they have the same length. -/
def K0LengthRelation (M M' : Type*) [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] : Prop :=
  Module.length R M = Module.length R M'

end Bertini
end
