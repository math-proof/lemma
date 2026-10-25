/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWProbDualityClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWBxpAssembly.Part2
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
import Theorem.StatisticalMechanics.Code.Universality.KestenHalf
import Theorem.StatisticalMechanics.Code.TwoDim.SelfDualDichotomy
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box


theorem rpd_crossingPair_incompatible (ω : ConfigSpace (Sym2 (Site 2)))
    (e : Sym2 (Site 2)) :
    ¬ (ω e = true ∧ dualConfig ω (crossEdge e) = true) :=
  StatMech.RSW.crossingPair_incompatible ω e


theorem rpd_open_dualOpen_disjoint_crossPair (ω : ConfigSpace (Sym2 (Site 2)))
    {e : Sym2 (Site 2)} (he : ω e = true) :
    dualConfig ω (crossEdge e) = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  exact rpd_crossingPair_incompatible ω e ⟨he, h⟩


theorem rpd_crossWalks_no_sharedCrossPair (ω : ConfigSpace (Sym2 (Site 2)))
    {x y : Site 2} (w : (openSubgraph 2 ω).Walk x y)
    {x' y' : Site 2} (w' : (openSubgraph 2 (dualConfig ω)).Walk x' y')
    (e : Sym2 (Site 2)) (he : e ∈ w.edges) (he' : crossEdge e ∈ w'.edges) :
    False :=
  StatMech.RSW.openWalk_blocks_dualWalk ω w w' e he he'


theorem rpd_hCross_dualVCross_exclusive (ω : ConfigSpace (Sym2 (Site 2)))
    {xh yh : Site 2} (wh : (openSubgraph 2 ω).Walk xh yh)
    {xv yv : Site 2} (wv : (openSubgraph 2 (dualConfig ω)).Walk xv yv)
    (e : Sym2 (Site 2)) (he : e ∈ wh.edges) (he' : crossEdge e ∈ wv.edges) :
    False :=
  rpd_crossWalks_no_sharedCrossPair ω wh wv e he he'


theorem rpd_dualVerticalCrossing_eq (a b c d : ℤ)
    (hmeasV : MeasurableSet (verticalCrossingEvent a b c d)) :
    rba_selfDualMeasure.real (dualVerticalCrossingEvent a b c d)
      = rba_selfDualMeasure.real (verticalCrossingEvent a b c d) :=
  rba_dualVerticalCrossing_eq a b c d hmeasV


theorem rpd_square_reflection (n : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n)) :
    rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n)
      = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) :=
  crf_verticalCrossing_eq_horizontal_swap 0 n 0 n hmeasH


end Universality
end StatMech
