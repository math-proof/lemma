/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.OrbitInteriorOdd
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem jsp_odd_propagates_off_support (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (i : ℕ) {z₀ : Site 2}
    (p : (hypercubicLattice 2).Walk ((dartNext K)^[i] a.1).tail z₀)
    (hp : ∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK a.1 a.2).support)
    (hodd : ¬ Even (jec_rayCount z₀ (olb_orbitLoop K hK a.1 a.2))) :
    ¬ Even (jec_rayCount ((dartNext K)^[i] a.1).tail (olb_orbitLoop K hK a.1 a.2)) :=
  ooi_odd_of_connected_to_odd (olb_orbitLoop K hK a.1 a.2) p hp hodd


theorem jsp_tailOdd_of_oddCell_reaches_tail (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) {z₀ : Site 2} (i : ℕ)
    (p : (hypercubicLattice 2).Walk ((dartNext K)^[i] a.1).tail z₀)
    (hp : ∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK a.1 a.2).support)
    (hodd : ¬ Even (jec_rayCount z₀ (olb_orbitLoop K hK a.1 a.2))) :
    wwit_TailOdd K hK a :=
  ⟨i, jsp_odd_propagates_off_support K hK a i p hp hodd⟩


end Lattice
end StatMech
