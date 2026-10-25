/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonTrifurcation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bfin2assemble
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Percolation.OutwardArmForestClose.Part3
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonTrifurcation.Part2


namespace StatMech.FrontierA

open Finset SimpleGraph Set

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.Percolation

open StatMech.Walls


variable {V : Type*} [Fintype V] [Nonempty V]


variable {d : ℕ}


@[simp] theorem mem_canonicalTrifurcationsInBox
    {omega : ConfigSpace (Sym2 (Site d))} {R : ℕ} {x : Site d} :
    x ∈ canonicalTrifurcationsInBox omega R ↔
      x ∈ box d (R - 1) ∧ IsCanonicalTrifurcation d omega x := by
  classical
  simp [canonicalTrifurcationsInBox]


theorem finite_canonical_trifurcation_count
    (omega : ConfigSpace (Sym2 (Site d))) (R : ℕ) (hR : 1 ≤ R) :
    (canonicalTrifurcationsInBox omega R).card ≤
      (vertexBoundary_finite d R).toFinset.card := by
  classical
  have hsubset : canonicalTrifurcationsInBox omega R ⊆
      (bfin2_trifSet_finite omega R).toFinset := by
    intro x hx
    rw [mem_canonicalTrifurcationsInBox] at hx
    rw [Set.Finite.mem_toFinset]
    exact ⟨fineTrifurcation_of_canonical omega x hx.2, hx.1⟩
  exact (Finset.card_le_card hsubset).trans (bfin2_count omega R hR)

end StatMech.FrontierA
