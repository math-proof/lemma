/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.ZMod.Basic
import Def.v1.Atlas.EllipticCurves.code.RingClassField.Part3
import Lemma.Complex.Atlas.v1.EllipticCurves.code.RingClassField
import Lemma.Complex.Atlas.v1.EllipticCurves.code.HilbertClassPolynomial
import Def.v1.Atlas.EllipticCurves.code.HilbertClassPolynomial.Part2
import Def.v1.Atlas.EllipticCurves.code.IsogenyVolcano.Part4
/-- A multigraph on vertex set `V`: each unordered pair `(v, w)` carries a
multiplicity `edgeMult v w : ℕ`, required to be symmetric in `v, w`. -/
/-- Two vertices `v, w` are adjacent in `G` iff their edge multiplicity is positive. -/
/-- The classical modular polynomial `Φ_ℓ(X, Y)` specialized to `Y = j₁`: a univariate
polynomial in `X` over `k` whose roots over an algebraic closure are the `j`-invariants
of elliptic curves `ℓ`-isogenous to a curve with `j`-invariant `j₁`. -/


namespace Multigraph

variable {V : Type*} (G : Multigraph V)

end Multigraph

noncomputable section

open Polynomial Finset

namespace CMConductorTrichotomy

variable {C : OrdinaryIsogenyComponent} (K : KohelVolcano C)

/-- Counts of `ℓ`-isogenies from a CM elliptic curve over `F` (with `|F| = q`):
horizontal, ascending, and descending counts, with the values prescribed by
Theorem 22.5, and the descending count conditioned on whether descendant CM
curves exist over `F`. -/
structure IsogenyCount (C : CMCurveData) (F : Type*) [Field F] [Fintype F] where
  hcard : Fintype.card F = C.q
  hne : (ellCMSet C.D F).Nonempty
  numHorizontal : ℕ
  numAscending : ℕ
  numDescending : ℕ
  horizontal_eq : (numHorizontal : ℤ) = 1 + jacobiSym C.D C.ℓ
  ascending_eq : numAscending = if C.ℓ ∣ C.f then 1 else 0
  descending_zero_of_empty :
    (ellCMSet C.descendantDisc F) = ∅ → numDescending = 0
  descending_eq_of_nonempty :
    (ellCMSet C.descendantDisc F).Nonempty →
    (numDescending : ℤ) = ↑C.ℓ - jacobiSym C.D C.ℓ

/-- Existence of an `IsogenyCount` package for any CM data with a nonempty CM set
over `F`. -/

end IsogenyCount

namespace CMTorsor

open Elliptic_Curves Elliptic_Curves.Deuring

/-- Data for a CM torsor: an imaginary quadratic discriminant `D` and a prime power
`q` coprime to `|D|`. -/
structure CMTorsorData where
  D : ℤ
  hD : IsImagQuadDiscriminant D
  q : ℕ
  hq : 1 < q
  hcop : Nat.Coprime q D.natAbs

end CMTorsor
end
