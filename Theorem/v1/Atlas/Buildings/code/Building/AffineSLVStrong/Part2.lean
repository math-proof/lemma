module
public import Def.v1.Atlas.Buildings.code.Building.AffineSLV.Part4
public import Theorem.Set.IsHomothetic_πLattice
public import Theorem.Set.ConjSet.eq.Image
public import Structure.v1.Atlas.Buildings.code.Building.GroupApplicationsCh17
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Group.Matrix
public import Def.v1.Atlas.Buildings.code.Building.AffineSLVStrong.Part2
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
