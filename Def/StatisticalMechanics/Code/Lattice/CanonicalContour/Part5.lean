/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CanonicalContour.Part4
open Finset Set SimpleGraph Function MeasureTheory
open scoped NNReal ENNReal BigOperators


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin percolationEvent mem_percolationEvent)

variable {ω : ConfigSpace (Sym2 (Site 2))}


def CanonicalContourWinds (ω : ConfigSpace (Sym2 (Site 2)))
    (hfin : (cluster 2 ω (origin 2)).Finite) : Prop :=
  exitIndex (ω := ω) hfin
    < dartOrbitPeriod (cluster 2 ω (origin 2))
        ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩


noncomputable def canonicalFaceWalkAux (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) :
    (n : ℕ) → (faceBoundaryGraph K).Walk (dartFace e) (dartFace ((dartNext K)^[n] e))
  | 0 => SimpleGraph.Walk.nil
  | (n + 1) =>
      (canonicalFaceWalkAux K e he n).concat (by
        rw [Function.iterate_succ_apply']
        exact dartFace_step_adj K _ (iterate_isBoundaryDart K e he n))


end Lattice
end StatMech
