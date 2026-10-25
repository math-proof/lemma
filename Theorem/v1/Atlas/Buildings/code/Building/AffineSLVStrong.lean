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
import Def.v1.Atlas.Buildings.code.Building.AffineSLVStrong
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace AffineBuildingSLVStrong

open AffineBuildingSLV AffineBuildingSLVAxioms


/-- Each standard basis vector $e_j$ is nonzero. -/
theorem stdBasisVec_ne_zero (C : DVRContext) (j : Fin C.n) : stdBasisVec C j ≠ 0 := by
  intro h
  have : stdBasisVec C j j = (0 : Fin C.n → C.k) j := by rw [h]
  simp [stdBasisVec] at this

end AffineBuildingSLVStrong
