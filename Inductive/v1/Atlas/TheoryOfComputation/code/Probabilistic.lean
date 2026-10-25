/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Polynomial.Roots
import Def.v1.Atlas.TheoryOfComputation.code.BPP.Part3
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.Order.Archimedean.Basic
import Def.v1.Atlas.TheoryOfComputation.code.Probabilistic.Part2


namespace Probabilistic

/-- A node of a branching program with `m` input variables and `N` total nodes.
A node is either a `query` on variable `var : Fin m` with two successors `zero,
one : Fin N` (followed depending on whether the bit is `0` or `1`), or an
`output` leaf carrying a Boolean answer. -/
inductive BPNode (m : ℕ) (N : ℕ) where
  | query (var : Fin m) (zero : Fin N) (one : Fin N) : BPNode m N
  | output (val : Bool) : BPNode m N

end Probabilistic
