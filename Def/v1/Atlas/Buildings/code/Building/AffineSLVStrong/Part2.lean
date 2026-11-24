module
public import Def.v1.Atlas.Buildings.code.Building.AffineSLV.Part4
public import Lemma.Set.IsHomothetic_πLattice
public import Theorem.Set.ConjSet.eq.Image
public import Structure.v1.Atlas.Buildings.code.Building.GroupApplicationsCh17
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Group.Matrix
public import Theorem.v1.Atlas.Buildings.code.Building.AffineSLVStrong
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


/-- The $j$-th coordinate line $k \cdot e_j$ in $k^n$, packaged as a Line. -/
noncomputable def stdLine (C : DVRContext) (j : Fin C.n) : Line C :=
  ⟨stdBasisVec C j, stdBasisVec_ne_zero C j⟩

end AffineBuildingSLVStrong
