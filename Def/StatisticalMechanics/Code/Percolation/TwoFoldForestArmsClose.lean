/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TwoFoldForestArmsClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeRealiseClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.TwoFoldHallClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.TwoFoldForestArmsClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


open Classical in


def tffa_ValidBranch (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (u : Site d) : Prop :=
  (cluster d (removeSites (tfc_trifFinset ω n) ω) u).Infinite

open Classical in


def tffa_TwoFoldClawConfig (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (x₀ : Site d) (y : Fin 3 → Site d) (κ : Site d → Fin 6),
    (x₀ ∈ box d n ∧ IsTrifurcation d ω x₀) ∧
    (∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i) ∧
    Function.Injective y ∧
    
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i) ∧
    
    (∀ u v, tffa_ValidBranch ω n u → tffa_ValidBranch ω n v →
      κ u = κ v → aed_sameGlobalComponent (tfc_trifFinset ω n) ω u v)


end Percolation
end StatMech
