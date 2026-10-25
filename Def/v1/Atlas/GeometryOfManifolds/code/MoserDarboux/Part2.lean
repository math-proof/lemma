/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticStandardBasis
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HamiltonianVectorFields
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticEvenDim
import Theorem.v1.Atlas.GeometryOfManifolds.code.SymplecticStandardBasis
import Def.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields.Part3
import Class.v1.Atlas.GeometryOfManifolds.code.MoserDarboux
set_option autoImplicit false

universe u_chart v_chart

open Module FiniteDimensional Finset
open SymplecticLinearAlgebra
open DifferentialFormSpace


/-- Composition of DFS morphisms: given $f : (\Omega_1, VF_1) \to (\Omega_2, VF_2)$ and
$g : (\Omega_2, VF_2) \to (\Omega_3, VF_3)$, the composite pulls back via $g$ then $f$. -/
def DFSMorphism.comp
    {Ω₁ : ℕ → Type*} {VF₁ : Type*}
    {Ω₂ : ℕ → Type*} {VF₂ : Type*}
    {Ω₃ : ℕ → Type*} {VF₃ : Type*}
    [inst₁ : DifferentialFormSpace Ω₁ VF₁]
    [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    [inst₃ : DifferentialFormSpace Ω₃ VF₃]
    (g : DFSMorphism Ω₂ VF₂ Ω₃ VF₃)
    (f : DFSMorphism Ω₁ VF₁ Ω₂ VF₂) :
    DFSMorphism Ω₁ VF₁ Ω₃ VF₃ where
  pullback α := f.pullback (g.pullback α)
  pullback_add α β := by rw [g.pullback_add, f.pullback_add]
  pullback_smul r α := by rw [g.pullback_smul, f.pullback_smul]
  pullback_comm_d α := by rw [g.pullback_comm_d, f.pullback_comm_d]


