/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Algebra.Polynomial.Roots
public import Def.v1.Atlas.TheoryOfComputation.code.BPP.Part3
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Def.v1.Atlas.TheoryOfComputation.code.Probabilistic.Part3


public section

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
