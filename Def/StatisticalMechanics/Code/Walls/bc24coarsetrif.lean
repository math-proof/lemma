/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc24coarsetrif.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc21trifurc.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc24coarsetrif
open Set SimpleGraph MeasureTheory
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def IsCoarseTrifurcation (d n : ℕ) (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    (b₁ ∈ box d n ∧ b₂ ∈ box d n ∧ b₃ ∈ box d n) ∧
    ((hypercubicLattice d).Adj a₁ b₁ ∧ (hypercubicLattice d).Adj a₂ b₂ ∧
      (hypercubicLattice d).Adj a₃ b₃) ∧
    (Connected d ω a₁ b₁ ∧ Connected d ω a₂ b₂ ∧ Connected d ω a₃ b₃) ∧
    ((cluster d (removeSites (boxFinsetBK d n) ω) a₁).Infinite ∧
      (cluster d (removeSites (boxFinsetBK d n) ω) a₂).Infinite ∧
      (cluster d (removeSites (boxFinsetBK d n) ω) a₃).Infinite) ∧
    (¬ Connected d (removeSites (boxFinsetBK d n) ω) a₁ a₂ ∧
      ¬ Connected d (removeSites (boxFinsetBK d n) ω) a₁ a₃ ∧
      ¬ Connected d (removeSites (boxFinsetBK d n) ω) a₂ a₃)


end StatMech.Walls
