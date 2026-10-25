/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.InteriorOrientation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness.Part3
import Def.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part2
open Set SimpleGraph


namespace StatMech

namespace Lattice

theorem exc_interiorSubset_of_reaches_and_support (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hoff : exc_OffSupportReachesExterior K a)
    (hsupp : exc_SupportOddInK K a) :
    eaw_InteriorSubset K a := by
  intro z hodd
  by_cases hzsupp : z ∈ (mpl_orbitLoop K a).support
  · exact hsupp z hzsupp hodd
  · by_contra hzK
    obtain ⟨z0, p, hp, hfar⟩ := exc_offSupport_of_reaches K a hoff z hzK hzsupp
    have hbase : Even (jec_rayCount z0 (mpl_orbitLoop K a)) := by
      rw [jec_rayCount_eq_zero_of_right z0 (mpl_orbitLoop K a) (fun q hq => hfar q hq)]
      exact Nat.even_iff.mpr rfl
    exact hodd ((oee_rayParity_const_along_walk (mpl_orbitLoop K a) p hp).mpr hbase)


theorem exc_unitCell_supportOddInK : exc_SupportOddInK unitCell ucBase := by
  intro z _ hodd
  exact eaw_unitCell_interiorSubset z hodd


theorem exc_exterior_self_reachable (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (R : ℕ) (hR : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (z : Site 2) (hz : z ∈ exterior 2 R) :
    ((hypercubicLattice 2).induce
        ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2))ᶜ).Reachable
      ⟨z, exterior_subset_compl _ R hR hz⟩ ⟨z, exterior_subset_compl _ R hR hz⟩ :=
  SimpleGraph.Reachable.refl _

end Lattice
end StatMech
