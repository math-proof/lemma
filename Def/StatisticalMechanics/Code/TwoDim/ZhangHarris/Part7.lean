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
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangHarris.Part6
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Percolation StatMech.Universality

open StatMech.RSW.Box

noncomputable def zih_sideSupport (F : Finset (Sym2 (Site 2))) (i : Fin 4) :
    Finset (Sym2 (Site 2)) :=
  match i with
  | 0 => F
  | 1 => zih_rotSupport (zih_rotSupport F)
  | 2 => zih_rotSupport F
  | 3 => zih_rotSupport (zih_rotSupport (zih_rotSupport F))

end StatMech.TwoDim
