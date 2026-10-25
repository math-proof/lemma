/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.TwoDim.ZhangRotSymmetry.Part3
import Theorem.StatisticalMechanics.Code.Walls.binsclosure.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part5
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation StatMech.Walls


def zbd_centeredLeftSide (n : ℕ) : Set (Site 2) :=
  {x | x ∈ box 2 n ∧ x 0 = -(n : ℤ)}

def zbd_centeredRightSide (n : ℕ) : Set (Site 2) :=
  {x | x ∈ box 2 n ∧ x 0 = (n : ℤ)}

def zbd_centeredBottomSide (n : ℕ) : Set (Site 2) :=
  {x | x ∈ box 2 n ∧ x 1 = -(n : ℤ)}

def zbd_centeredTopSide (n : ℕ) : Set (Site 2) :=
  {x | x ∈ box 2 n ∧ x 1 = (n : ℤ)}


noncomputable def zbd_rotOpenIso (omega : ConfigSpace (Sym2 (Site 2))) :
    openSubgraph 2 (kdi_rotConfig omega) ≃g openSubgraph 2 omega where
  toEquiv := rot90Equiv.symm
  map_rel_iff' := by
    intro x y
    constructor
    · rintro ⟨hadj, hopen⟩
      refine ⟨(rot90Iso.symm.map_rel_iff (a := x) (b := y)).mp hadj, ?_⟩
      simpa [zrs_rotConfig_apply, kdi_rotEdgeEquiv, StatMech.Lattice.sym2Congr] using hopen
    · rintro ⟨hadj, hopen⟩
      refine ⟨(rot90Iso.symm.map_rel_iff (a := x) (b := y)).mpr hadj, ?_⟩
      simpa [zrs_rotConfig_apply, kdi_rotEdgeEquiv, StatMech.Lattice.sym2Congr] using hopen

end StatMech.TwoDim
