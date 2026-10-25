/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeRealiseClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


variable {N : Type*} [Fintype N] [DecidableEq N]

def str_ForestLeafSelection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (r₀ : Site d) (ℓ : Site d → Fin 2 → Site d),
    r₀ ∈ vertexBoundary d n ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ j, ℓ x j ∈ vertexBoundary d n) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ j, Connected d ω x (ℓ x j)) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ j, ℓ x j ≠ r₀) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      ∀ j j', ℓ x j = ℓ y j' → x = y ∧ j = j')


end Percolation
end StatMech
