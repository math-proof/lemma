/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorOrientation.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem ior_rayCount_eq_zero_of_farLeft (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hfar : ∀ p ∈ (mpl_orbitLoop K a).support, z 0 ≤ p 0) :
    jec_rayCount z (mpl_orbitLoop K a) = 0 :=
  jec_rayCount_eq_zero_of_right z (mpl_orbitLoop K a) hfar


theorem ior_farLeft_even (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hfar : ∀ p ∈ (mpl_orbitLoop K a).support, z 0 ≤ p 0) :
    Even (jec_rayCount z (mpl_orbitLoop K a)) := by
  rw [ior_rayCount_eq_zero_of_farLeft K a z hfar]; exact Nat.even_iff.mpr rfl


theorem ior_exterior_even (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {z z0 : Site 2} (p : (hypercubicLattice 2).Walk z z0)
    (hp : ∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support)
    (hfar : ∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0) :
    Even (jec_rayCount z (mpl_orbitLoop K a)) := by
  have hbase : Even (jec_rayCount z0 (mpl_orbitLoop K a)) := ior_farLeft_even K a z0 hfar
  exact (oee_rayParity_const_along_walk (mpl_orbitLoop K a) p hp).mpr hbase


end Lattice
end StatMech
