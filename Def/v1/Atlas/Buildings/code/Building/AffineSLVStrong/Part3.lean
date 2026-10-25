/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.AffineSLV.Part4
import Lemma.Set.IsHomothetic_πLattice
import Lemma.Set.ConjSet.eq.Image
import Structure.v1.Atlas.Buildings.code.Building.GroupApplicationsCh17
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Topology.Algebra.Group.Matrix
import Theorem.v1.Atlas.Buildings.code.Building.AffineSLVStrong.Part2
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace AffineBuildingSLVStrong

open AffineBuildingSLV AffineBuildingSLVAxioms


/-- The standard frame in $k^n$ consisting of the coordinate lines $k \cdot e_j$. -/
noncomputable def stdFrame (C : DVRContext) : Frame C where
  lines := stdLine C
  spans := by
    intro v
    exact ⟨v, (sum_std_basis_eq C v).symm⟩
  independent := by
    intro coeffs h j
    have hj : (fun i => ∑ k_1, coeffs k_1 * (stdLine C k_1).generator i) j
              = (0 : Fin C.n → C.k) j := congr_fun h j
    simp only [stdLine, Pi.zero_apply] at hj
    rw [sum_std_basis_apply] at hj
    exact hj


end AffineBuildingSLVStrong
