/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc89genuinetrifae.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc88genuinecount
import Theorem.StatisticalMechanics.Code.Walls.bc85bootstrap
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc89_GenuineTrif (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Prop :=
  ∃ a₁ a₂ a₃ : Site d,
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    (a₁ ≠ x ∧ a₂ ≠ x ∧ a₃ ≠ x) ∧
    ((openSubgraph d ω).Adj x a₁ ∧ (openSubgraph d ω).Adj x a₂ ∧ (openSubgraph d ω).Adj x a₃) ∧
    ((cluster d (removeSite x ω) a₁).Infinite ∧ (cluster d (removeSite x ω) a₂).Infinite ∧
      (cluster d (removeSite x ω) a₃).Infinite) ∧
    (¬ Connected d (removeSite x ω) a₁ a₂ ∧
      ¬ Connected d (removeSite x ω) a₁ a₃ ∧
      ¬ Connected d (removeSite x ω) a₂ a₃)


noncomputable def bc89_genuineTrifFinset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    Finset (Site d) := by
  classical
  exact (boxFinsetBK d n).filter (fun x => bc89_GenuineTrif d ω x)


noncomputable def bc89_genuineTcount (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : ℕ :=
  (bc89_genuineTrifFinset ω n).card


end StatMech.Walls
