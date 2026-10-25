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
import Def.v1.Atlas.Buildings.code.Building.AffineSLVStrong.Part2
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace AffineBuildingSLVStrong

open AffineBuildingSLV AffineBuildingSLVAxioms


/-- Pointwise evaluation: $(\sum_j c_j e_j)(i) = c_i$. -/
theorem sum_std_basis_apply (C : DVRContext) (coeffs : Fin C.n → C.k) (i : Fin C.n) :
    (∑ j, coeffs j * stdBasisVec C j i) = coeffs i := by
  rw [Finset.sum_eq_single i]
  · simp [stdBasisVec]
  · intro j _ hji
    simp [stdBasisVec, Ne.symm hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Functional form: $\sum_j c_j e_j = c$ as vectors in $k^n$. -/
theorem sum_std_basis_eq (C : DVRContext) (coeffs : Fin C.n → C.k) :
    (fun i => ∑ j, coeffs j * stdBasisVec C j i) = coeffs := by
  funext i
  exact sum_std_basis_apply C coeffs i

end AffineBuildingSLVStrong
