module
public import Def.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part6
public import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
public import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
public import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
public import Theorem.StatisticalMechanics.Code.Universality.KestenBXPWire
public import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part3
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


noncomputable def zfk_shiftRightHom (N : ℕ)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    openSubgraphInduce 2 (translateConfig (![1, 0] : Site 2) omega)
        (zfk_leftSquare N) →g
      openSubgraphInduce 2 omega (zfk_rightSquare N) where
  toFun := fun x => ⟨(x : Site 2) + ![1, 0],
    (zfk_shift_mem_rightSquare_iff N x).mp x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy ⊢
    exact (cti_isOpenEdge_translate (![1, 0] : Site 2) omega x y).mp hxy

noncomputable def zfk_shiftRightHomInv (N : ℕ)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    openSubgraphInduce 2 omega (zfk_rightSquare N) →g
      openSubgraphInduce 2 (translateConfig (![1, 0] : Site 2) omega)
        (zfk_leftSquare N) where
  toFun := fun x => ⟨(x : Site 2) - ![1, 0], by
    rw [zfk_shift_mem_rightSquare_iff N]
    simpa only [sub_add_cancel] using x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy ⊢
    apply (cti_isOpenEdge_translate (![1, 0] : Site 2) omega
      ((x : Site 2) - ![1, 0]) ((y : Site 2) - ![1, 0])).mpr
    simpa only [sub_add_cancel] using hxy

end StatMech.TwoDim
