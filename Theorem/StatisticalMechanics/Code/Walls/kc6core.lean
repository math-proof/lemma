/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.kc5_core.Part2
import Theorem.StatisticalMechanics.Code.Walls.kc6evenoddrule
import Theorem.StatisticalMechanics.Code.Walls.kc6uniqueinfinitecomponent
import Theorem.StatisticalMechanics.Code.Walls.kc6cornercellodd
import Theorem.StatisticalMechanics.Code.Walls.kc6windingwitness
import Theorem.StatisticalMechanics.Code.Walls.kc3_core
import Theorem.StatisticalMechanics.Code.Walls.kc3_oddrayeqleftRegion.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitnessClose
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem kc6_interiorSubset_of_halves (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hoff : exc_OffSupportReachesExterior K a)
    (hsupp : exc_SupportOddInK K a) :
    eaw_InteriorSubset K a :=
  exc_interiorSubset_of_reaches_and_support K a hoff hsupp


theorem kc6_leftRegion_subset_of_halves (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hoff : exc_OffSupportReachesExterior K a)
    (hsupp : exc_SupportOddInK K a) :
    jec_leftRegion (mpl_orbitLoop K a) ⊆ K := by
  intro z hz
  rw [jec_mem_leftRegion] at hz
  exact kc6_interiorSubset_of_halves K a hoff hsupp z hz


end Walls
end StatMech
