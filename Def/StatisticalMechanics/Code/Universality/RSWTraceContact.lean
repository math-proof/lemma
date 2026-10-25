/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceContact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def rlc_OppositeLoopSides {a : Site 2}
    (C : (hypercubicLattice 2).Walk a a) (x y : Site 2) : Prop :=
  (Even (jec_rayCount x C) ∧ ¬ Even (jec_rayCount y C)) ∨
    (¬ Even (jec_rayCount x C) ∧ Even (jec_rayCount y C))


end Universality
end StatMech
