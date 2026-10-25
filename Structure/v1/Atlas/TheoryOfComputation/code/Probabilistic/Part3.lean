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
import Inductive.v1.Atlas.TheoryOfComputation.code.Probabilistic


namespace Probabilistic

/-- A branching program on `m` Boolean input variables. It has `numNodes`
nodes (with node `0` being the start node) and a `nodes` table assigning each
index a `BPNode`. -/
structure BranchingProgram (m : ℕ) where
  numNodes : ℕ
  numNodes_pos : 0 < numNodes
  nodes : Fin numNodes → BPNode m numNodes

end Probabilistic
