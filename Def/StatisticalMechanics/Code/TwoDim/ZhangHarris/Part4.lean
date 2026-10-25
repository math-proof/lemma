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
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangHarris.Part3
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Percolation StatMech.Universality

open StatMech.RSW.Box

noncomputable def zih_rightSquareFinset (N : ℕ) : Finset (Site 2) :=
  (rect_finite (-(N : ℤ) + 1) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)).toFinset

noncomputable def zih_rightSquareEdges (N : ℕ) : Finset (Sym2 (Site 2)) :=
  edgesWithinFinset (zih_rightSquareFinset N)

end StatMech.TwoDim
