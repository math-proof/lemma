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
import Def.v1.Atlas.EllipticCurves.code.IsogenyVolcano.Part3
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

/-- Data for counting `ℓ`-isogenies from a CM elliptic curve over `𝔽_q`: an
imaginary quadratic discriminant `D` with class data, a prime `ℓ ∤ q` coprime to
`|D|`, and a conductor `f`. -/
structure CMCurveData where
  D : ℤ
  hD : IsImagQuadDiscriminant D
  ℓ : ℕ
  hℓ_prime : Nat.Prime ℓ
  q : ℕ
  hq : 1 < q
  hℓ_ndvd_q : ¬(ℓ ∣ q)
  hcop : Nat.Coprime q D.natAbs
  f : ℕ
  hf_pos : 0 < f

end CMConductorTrichotomy
end
