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
import Class.v1.Atlas.Buildings.code.Building.AffineSLVStrong
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace AffineBuildingSLVStrong

open AffineBuildingSLV AffineBuildingSLVAxioms


/-- The $j$-th standard basis vector $e_j \in k^n$. -/
noncomputable def stdBasisVec (C : DVRContext) (j : Fin C.n) : Fin C.n → C.k :=
  fun i => if i = j then 1 else 0

end AffineBuildingSLVStrong
