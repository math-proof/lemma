module
public import Theorem.StatisticalMechanics.Code.Probability.InfiniteHarris.Part3
public import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part12
public import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
public import Theorem.StatisticalMechanics.Code.TwoDim.ZhangHarris
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Percolation StatMech.Universality

open StatMech.RSW.Box

noncomputable def zih_leftSquareFinset (N : ℕ) : Finset (Site 2) :=
  (rect_finite (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)).toFinset

noncomputable def zih_leftSquareEdges (N : ℕ) : Finset (Sym2 (Site 2)) :=
  edgesWithinFinset (zih_leftSquareFinset N)

end StatMech.TwoDim
