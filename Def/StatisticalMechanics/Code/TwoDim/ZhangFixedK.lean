/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part6
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.KestenBXPWire
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


noncomputable def zfk_rotBoxIso
    (omega : ConfigSpace (Sym2 (Site 2))) (N : ℕ) :
    openSubgraphInduce 2 (kdi_rotConfig omega) (box 2 N) ≃g
      openSubgraphInduce 2 omega (box 2 N) where
  toEquiv :=
    { toFun := fun x => ⟨rot90Inv x, rot90Inv_mem_box N x.2⟩
      invFun := fun x => ⟨rot90Fun x, rot90Fun_mem_box N x.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact Equiv.apply_symm_apply rot90Equiv x
      right_inv := fun x => by
        apply Subtype.ext
        exact Equiv.symm_apply_apply rot90Equiv x }
  map_rel_iff' := by
    intro x y
    simp only [openSubgraphInduce_adj]
    exact (zbd_rotOpenIso omega).map_rel_iff

end StatMech.TwoDim
