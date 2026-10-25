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
import Def.StatisticalMechanics.Code.Percolation.BurtonKeane
open MeasureTheory

set_option linter.style.show false


namespace StatMech

namespace Percolation

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


@[simp] lemma translateHomInv_apply (g : Multiplicative (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (a : Site d) : translateHomInv g ω a = g⁻¹ • a := rfl


lemma connected_shift (g : Multiplicative (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (x y : Site d) :
    Connected d (shift g ω) (g • x) (g • y) ↔ Connected d ω x y := by
  constructor
  · intro h
    have h2 := SimpleGraph.Reachable.map (translateHomInv g ω) h
    simp only [translateHomInv_apply, inv_smul_smul] at h2
    exact h2
  · intro h
    exact SimpleGraph.Reachable.map (translateHom g ω) h


lemma cluster_shift (g : Multiplicative (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) :
    cluster d (shift g ω) (g • x) = (fun y => g • y) '' (cluster d ω x) := by
  ext z
  simp only [mem_cluster, Set.mem_image]
  constructor
  · intro h
    refine ⟨g⁻¹ • z, ?_, by rw [smul_inv_smul]⟩
    have hz : Connected d (shift g ω) (g • x) (g • (g⁻¹ • z)) := by rwa [smul_inv_smul]
    exact (connected_shift g ω x (g⁻¹ • z)).mp hz
  · rintro ⟨y, hy, rfl⟩
    exact (connected_shift g ω x y).mpr hy


end Percolation
end StatMech
