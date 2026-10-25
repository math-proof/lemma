/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_oddrayeqleftRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part3
import Theorem.StatisticalMechanics.Code.Walls.kc2_core.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem kc3_leftRegion_eq_oddRay {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    jec_leftRegion Vc = {z : Site 2 | ¬ Even (jec_rayCount z Vc)} := rfl


theorem kc3_mem_leftRegion_iff_oddRay {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (z : Site 2) : z ∈ jec_leftRegion Vc ↔ ¬ Even (jec_rayCount z Vc) :=
  jec_mem_leftRegion Vc z


theorem kc3_evenRay_iff_not_mem_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (z : Site 2) : Even (jec_rayCount z Vc) ↔ z ∉ jec_leftRegion Vc := by
  rw [kc3_mem_leftRegion_iff_oddRay]; exact (not_not).symm


theorem kc3_mem_orbitLeftRegion_iff_oddRay (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2) :
    z ∈ jec_leftRegion (mpl_orbitLoop K a) ↔ ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) :=
  jec_mem_leftRegion (mpl_orbitLoop K a) z


end Walls
end StatMech
