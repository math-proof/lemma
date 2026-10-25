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
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangHarris.Part2
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Percolation StatMech.Universality

open StatMech.RSW.Box

def zih_LeftArmApprox (k N m : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  ⋃ x : zfk_leftCentralFinset k,
    zih_clusterApprox (x : Site 2) m ∩ {omega | zfk_LeftArmFrom omega x N}

noncomputable def zih_leftApproxSupport (k N m : ℕ) :
    Finset (Sym2 (Site 2)) :=
  zih_leftSquareEdges N ∪
    (zfk_leftCentralFinset k).biUnion (fun x => zih_clusterSupport x m)

end StatMech.TwoDim
