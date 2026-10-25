/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.FaceDualDichotomy
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part6
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


noncomputable def fci_latticeEdgeEquiv : (hypercubicLattice 2).edgeSet ≃
    (hypercubicLattice 2).edgeSet :=
  Equiv.ofBijective fci_sharedEdgeMap
    ⟨fci_sharedEdgeMap_injective, fci_sharedEdgeMap_surjective⟩


noncomputable def fci_extendLatticeEdgeEquiv
    (e : (hypercubicLattice 2).edgeSet ≃ (hypercubicLattice 2).edgeSet) :
    Sym2 (Site 2) ≃ Sym2 (Site 2) where
  toFun x := if hx : x ∈ (hypercubicLattice 2).edgeSet then (e ⟨x, hx⟩ : Sym2 (Site 2)) else x
  invFun x := if hx : x ∈ (hypercubicLattice 2).edgeSet then (e.symm ⟨x, hx⟩ : Sym2 (Site 2)) else x
  left_inv x := by
    by_cases hx : x ∈ (hypercubicLattice 2).edgeSet
    · simp only [hx, dite_true]
      rw [dif_pos (e ⟨x, hx⟩).2]
      exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
    · change (if _ : (if _ : x ∈ (hypercubicLattice 2).edgeSet then _ else x) ∈
          (hypercubicLattice 2).edgeSet then _ else _) = x
      simp [hx]
  right_inv x := by
    by_cases hx : x ∈ (hypercubicLattice 2).edgeSet
    · simp only [hx, dite_true]
      rw [dif_pos (e.symm ⟨x, hx⟩).2]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
    · change (if _ : (if _ : x ∈ (hypercubicLattice 2).edgeSet then _ else x) ∈
          (hypercubicLattice 2).edgeSet then _ else _) = x
      simp [hx]


noncomputable def fci_faceEdgeEquiv : Sym2 (Site 2) ≃ Sym2 (Site 2) :=
  fci_extendLatticeEdgeEquiv fci_latticeEdgeEquiv

end Universality
end StatMech
