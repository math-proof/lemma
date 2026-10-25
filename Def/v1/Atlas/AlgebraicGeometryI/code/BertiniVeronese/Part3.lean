/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniVeronese.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Structure.v1.Atlas.AlgebraicGeometryI.code.BertiniVeronese


noncomputable section

open MvPolynomial Finset

namespace BertiniVeronese

/-- The intersection `X ∩ V(f)` is smooth (relative to `X`): at every nonzero point of `X` with
`f(x) = 0`, some partial derivative of `f` is nonzero. -/
def IsSmooth_intersection_variety {k : Type} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k)
    (X : SmoothProjectiveVariety k n) : Prop :=
  ∀ x : Fin (n + 1) → k, x ≠ 0 → X.onVariety x →
    MvPolynomial.eval x f = 0 →
    ∃ i : Fin (n + 1), MvPolynomial.eval x (MvPolynomial.pderiv i f) ≠ 0

/-- General version of smooth intersection: parameterized by predicates `onX` (point lies on `X`)
and `smoothX` (point is a smooth point of `X`). -/
def IsSmooth_intersection {k : Type} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k)
    (onX : (Fin (n + 1) → k) → Prop)
    (smoothX : (Fin (n + 1) → k) → Prop) : Prop :=
  ∀ x : Fin (n + 1) → k, x ≠ 0 → onX x → smoothX x →
    MvPolynomial.eval x f = 0 →
    ∃ i : Fin (n + 1), MvPolynomial.eval x (MvPolynomial.pderiv i f) ≠ 0

/-- The Veronese map sending `(t₀, …, tₙ)` to the tuple of all degree-`d` monomials `∏ tⱼ^{Iⱼ}`,
indexed by exponent vectors `I` with `|I| = d`. -/
def veroneseMap {k : Type} [CommSemiring k] (n d : ℕ)
    (t : Fin (n + 1) → k)
    (I : { s : Fin (n + 1) →₀ ℕ // s.sum (fun _ => id) = d }) : k :=
  Finset.univ.prod (fun j => t j ^ (I.val j))

end BertiniVeronese
end
