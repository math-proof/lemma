/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc41rootside.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc38acyclic.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc39spanning.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc40funnel.Part4
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc41_not_connected_removeSite_cutSite (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hxy : x ≠ y) : ¬ Connected d (removeSite y ω) x y := by
  rintro ⟨w⟩
  have hy_notin : y ∉ w.support := arc_walk_avoids_x hxy w
  exact hy_notin w.end_mem_support


theorem bc41_rootSideComparable_allPar_false (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hy0box : y₀ ∈ box d n) (htriy0 : IsTrifurcation d ω y₀)
    (hne : x₀ ≠ y₀) (hconn : Connected d ω x₀ y₀) :
    ¬ ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
        bc40_RootSideComparable ω n rank par := by
  intro hroot_side
  
  set rank : Site d → ℕ ×ₗ ℕ := fun z => toLex (if z = y₀ then 1 else 0, 0) with hrank
  set par : Site d → Site d := fun _ => y₀ with hpar
  have hlt : rank x₀ < rank y₀ := by
    simp only [hrank, if_neg hne, if_pos]
    exact stt_lex_lt_fst (by norm_num)
  
  have hforced : Connected d (removeSite y₀ ω) x₀ (par y₀) :=
    hroot_side rank par x₀ hx0box htri0 y₀ hy0box htriy0 hne hconn hlt hne
  simp only [hpar] at hforced
  exact bc41_not_connected_removeSite_cutSite ω hne hforced


end StatMech.Walls
