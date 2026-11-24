module
public import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
public import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
public import Theorem.StatisticalMechanics.Code.Inequalities.Harris
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
public import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
public import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part77
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
