module
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ZMod.Basic
public import Def.v1.Atlas.EllipticCurves.code.RingClassField.Part3
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.RingClassField
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.HilbertClassPolynomial
public import Def.v1.Atlas.EllipticCurves.code.HilbertClassPolynomial.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyVolcano.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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

namespace IsogenyGraph

/-- The multiplicity of `j₂` as a root of `Φ_ℓ(j₁, Y)`, equal to the number of
`ℓ`-isogenies (with multiplicity) from a curve with `j`-invariant `j₁` to one with
`j`-invariant `j₂`. -/
abbrev 𝔽_p_jInvariants (p : ℕ) : Type := ZMod p

end IsogenyGraph
end
