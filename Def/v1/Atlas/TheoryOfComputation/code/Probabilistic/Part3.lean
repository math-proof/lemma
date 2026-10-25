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
import Structure.v1.Atlas.TheoryOfComputation.code.Probabilistic.Part3


namespace Probabilistic

/-- Evaluate a branching program `bp` on a Boolean `assignment`. Execution
starts at node `0` and follows `query` edges according to the assignment; the
recursion is bounded by `bp.numNodes` units of fuel via the inner `go`. -/
def BranchingProgram.eval (bp : BranchingProgram m) (assignment : Fin m → Bool)
    : Bool :=
  go bp assignment ⟨0, bp.numNodes_pos⟩ bp.numNodes
where
  go (bp : BranchingProgram m) (assignment : Fin m → Bool)
      (node : Fin bp.numNodes) : ℕ → Bool
    | 0 => false
    | fuel + 1 =>
      match bp.nodes node with
      | BPNode.output val => val
      | BPNode.query var zero one =>
        if assignment var then go bp assignment one fuel
        else go bp assignment zero fuel

/-- Two branching programs are *equivalent* (`B₁ ≡ B₂`) if they compute the
same Boolean function: `bp₁.eval a = bp₂.eval a` for every assignment `a`. -/
def BPEquiv (bp₁ bp₂ : BranchingProgram m) : Prop :=
  ∀ assignment : Fin m → Bool, bp₁.eval assignment = bp₂.eval assignment

/-- A branching program is *read-once* if, along any computation path, each
input variable is queried at most once. Formally: for every list of nodes
`path` along which the program might step, any two indices `i, j` whose nodes
both `query` the same variable `v` must coincide. -/
def BranchingProgram.isReadOnce (bp : BranchingProgram m) : Prop :=
  ∀ (path : List (Fin bp.numNodes)),
    (∀ (i j : Fin path.length) (v : Fin m),
      (∃ z o, bp.nodes (path.get i) = BPNode.query v z o) →
      (∃ z o, bp.nodes (path.get j) = BPNode.query v z o) →
      i = j)

end Probabilistic
