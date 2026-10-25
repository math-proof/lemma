/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Instance.StatisticalMechanics.Code.Percolation.BurtonKeane
open MeasureTheory

set_option linter.style.show false


namespace StatMech

namespace Percolation

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


lemma smul_sym2_mk (g : Multiplicative (Site d)) (x y : Site d) :
    g • s(x, y) = s(g • x, g • y) := by
  show Sym2.map _ _ = _
  rw [Sym2.map_mk]


lemma smul_site_apply (g : Multiplicative (Site d)) (x : Site d) (i : Fin d) :
    (g • x) i = Multiplicative.toAdd g i + x i := rfl


lemma hyper_adj_smul (g : Multiplicative (Site d)) (x y : Site d) :
    (hypercubicLattice d).Adj (g • x) (g • y) ↔ (hypercubicLattice d).Adj x y := by
  simp only [hypercubicLattice_adj]
  have key : ∀ i : Fin d, ((g • x) i - (g • y) i).natAbs = (x i - y i).natAbs := by
    intro i
    rw [smul_site_apply, smul_site_apply]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun i _ => key i)]


lemma shift_apply_smul (g : Multiplicative (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (x y : Site d) : (shift g ω) s(g • x, g • y) = ω s(x, y) := by
  rw [shift_apply]
  congr 1
  show g⁻¹ • s(g • x, g • y) = s(x, y)
  rw [smul_sym2_mk]
  congr 1 <;> rw [inv_smul_smul]


lemma openSubgraph_adj_shift (g : Multiplicative (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d) :
    (openSubgraph d (shift g ω)).Adj (g • x) (g • y) ↔ (openSubgraph d ω).Adj x y := by
  simp only [openSubgraph_adj]
  rw [hyper_adj_smul, shift_apply_smul]


end Percolation
end StatMech
