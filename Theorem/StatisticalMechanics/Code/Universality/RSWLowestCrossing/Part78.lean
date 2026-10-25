/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part77
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_maskConfig_congr {U : Finset (Sym2 (Site 2))}
    {omega omega' : ConfigSpace (Sym2 (Site 2))}
    (h : ∀ e ∈ (U : Set (Sym2 (Site 2))), omega e = omega' e) :
    rlc_maskConfig U omega = rlc_maskConfig U omega' := by
  funext e
  by_cases he : e ∈ U
  · simp only [rlc_maskConfig, if_pos he]
    exact h e he
  · simp [rlc_maskConfig, he]

theorem rlc_maskConfig_mono (U : Finset (Sym2 (Site 2)))
    {omega omega' : ConfigSpace (Sym2 (Site 2))} (h : omega ≤ omega') :
    rlc_maskConfig U omega ≤ rlc_maskConfig U omega' := by
  intro e
  by_cases he : e ∈ U <;> simp [rlc_maskConfig, he, h e]


end Universality
end StatMech
