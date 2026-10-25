/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempPlus.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part7
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
open Finset SimpleGraph Set


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

noncomputable section

theorem ons_fvCutEdges_eq_crossEdges_minusSet
    {d : Nat} (B : Finset (Sym2 (Site d)))
    (config : ConfigSpace (Site d))
    (hB : ∀ e ∈ B, e ∈ (hypercubicLattice d).edgeSet) :
    ons_fvCutEdges B config = crossEdges (minusSet config) B := by
  classical
  ext e
  unfold ons_fvCutEdges crossEdges
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro heB
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : (hypercubicLattice d).Adj x y :=
        (SimpleGraph.mem_edgeSet _).mp (hB s(x, y) heB)
      rw [crosses_mk, bond_mk]
      cases hx : config x <;> cases hy : config y <;>
        norm_num [spin, minusSet, hx, hy]


end
end StatMech.Onsager
