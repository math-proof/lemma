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
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Percolation StatMech.Universality

open StatMech.RSW.Box

def zih_centerShift (x : Site 2) : Multiplicative (Site 2) :=
  Multiplicative.ofAdd (-x)

def zih_clusterApprox (x : Site 2) (m : ℕ) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  (ConfigSpace.shift (zih_centerShift x)) ⁻¹' crossingEvent 2 (m + 1)

noncomputable def zih_clusterSupport (x : Site 2) (m : ℕ) :
    Finset (Sym2 (Site 2)) :=
  (boxEdgeFinset 2 (m + 1)).image
    (fun e => (zih_centerShift x)⁻¹ • e)

end StatMech.TwoDim
