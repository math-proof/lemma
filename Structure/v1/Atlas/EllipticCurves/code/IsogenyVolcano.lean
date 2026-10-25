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
import Def.v1.Atlas.EllipticCurves.code.IsogenyVolcano.Part2
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

/-- Data attached to a CM `ℓ`-isogeny problem: an imaginary quadratic discriminant
`D < 0`, a prime `ℓ`, and a positive conductor `f` of the source order. -/
structure CMIsogenyData where
  D : ℤ
  hD_neg : D < 0
  ℓ : ℕ
  hℓ_prime : Nat.Prime ℓ
  f : ℕ
  hf_pos : 0 < f

/-- Counts of `ℓ`-isogenies from a surface (`ℓ ∤ f`) CM elliptic curve, organized by
type. Following Theorem 22.5, there are `1 + (D/ℓ)` horizontal, `ℓ - (D/ℓ)`
descending, and `0` ascending isogenies. -/
structure SurfaceIsogenyCounts (C : CMIsogenyData) where
  hℓ_ndvd_f : ¬(C.ℓ ∣ C.f)
  numHorizontal : ℕ
  numDescending : ℕ
  numAscending : ℕ
  horizontal_eq : (numHorizontal : ℤ) = 1 + jacobiSym C.D C.ℓ
  descending_eq : (numDescending : ℤ) = ↑C.ℓ - jacobiSym C.D C.ℓ
  ascending_eq : numAscending = 0

/-- Counts of `ℓ`-isogenies from a non-surface (`ℓ ∣ f`) CM elliptic curve: `0`
horizontal, `ℓ` descending, and `1` ascending. -/
structure NonSurfaceIsogenyCounts (C : CMIsogenyData) where
  hℓ_dvd_f : C.ℓ ∣ C.f
  numHorizontal : ℕ
  numDescending : ℕ
  numAscending : ℕ
  horizontal_eq : numHorizontal = 0
  descending_eq : numDescending = C.ℓ
  ascending_eq : numAscending = 1

/-- Data for an ordinary component of the `ℓ`-isogeny graph over `𝔽_q`: a prime `ℓ`
coprime to `q`, the Hasse trace `t` (with `t² < 4q`), a fundamental imaginary
quadratic discriminant `D₀`, a positive base conductor `f₀`, and the class number. -/
structure OrdinaryIsogenyComponent where
  q : ℕ
  ℓ : ℕ
  hℓ_prime : Nat.Prime ℓ
  hℓ_ndvd_q : ¬(ℓ ∣ q)
  t : ℤ
  hHasse : t ^ 2 < 4 * (q : ℤ)
  D₀ : ℤ
  hD₀_neg : D₀ < 0
  f₀ : ℕ
  hf₀_pos : 0 < f₀
  classOrder : ℕ
  hClassOrder_pos : 0 < classOrder

end CMConductorTrichotomy
end
