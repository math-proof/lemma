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
public import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part66
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


theorem rlc_rightCommonSupport_nonempty_of_not_disjoint {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1)) :
    (rlc_rightCommonSupport gamma delta).Nonempty := by
  classical
  obtain ⟨z, hzGamma, hzDelta⟩ := Finset.not_disjoint_iff.mp hinter
  simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hzGamma hzDelta
  obtain ⟨u, huGamma, huz⟩ := hzGamma
  obtain ⟨v, hvDelta, hvz⟩ := hzDelta
  have huv : u = v := by
    apply Subtype.ext
    exact huz.trans hvz.symm
  subst v
  refine ⟨u, ?_⟩
  simp [rlc_rightCommonSupport, huGamma, hvDelta]


end Universality
end StatMech
