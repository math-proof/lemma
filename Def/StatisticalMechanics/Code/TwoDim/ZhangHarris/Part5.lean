/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InfiniteHarris.Part3
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part12
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangHarris.Part4
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Percolation StatMech.Universality

open StatMech.RSW.Box

def zih_RightArmApprox (k N m : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  ⋃ y : zfk_rightCentralFinset k,
    zih_clusterApprox (y : Site 2) m ∩ {omega | zfk_RightArmFrom omega y N}

noncomputable def zih_rightApproxSupport (k N m : ℕ) :
    Finset (Sym2 (Site 2)) :=
  zih_rightSquareEdges N ∪
    (zfk_rightCentralFinset k).biUnion (fun y => zih_clusterSupport y m)

end StatMech.TwoDim
