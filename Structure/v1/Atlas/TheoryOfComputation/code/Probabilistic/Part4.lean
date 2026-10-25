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
import Def.v1.Atlas.TheoryOfComputation.code.Probabilistic.Part3


namespace Probabilistic

/-- A description of a pair `(B₁, B₂)` of read-once branching programs on the
same number of variables, together with proofs that each is read-once. This is
the mathematical object whose equivalence problem is `EQ_ROBP`. -/
structure ROBPPairDesc where
  numVars : ℕ
  B₁ : BranchingProgram numVars
  B₂ : BranchingProgram numVars
  B₁_readOnce : B₁.isReadOnce
  B₂_readOnce : B₂.isReadOnce

end Probabilistic
