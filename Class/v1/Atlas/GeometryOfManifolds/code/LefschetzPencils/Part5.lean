/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HodgeTheory
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part12
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Structure.v1.Atlas.GeometryOfManifolds.code.LefschetzPencils.Part4
set_option autoImplicit false

open DifferentialFormSpace


/-- **Symplectic sum (existence).**

Given two symplectic manifolds $(M_1, \omega_1)$, $(M_2, \omega_2)$ and a common
codimension-2 symplectic submanifold $Q$ with inclusions pulling back the ambient
symplectic forms to $\omega_Q$, there exists a new symplectic manifold $R$ with
embeddings $j_k : M_k \hookrightarrow R$ such that $j_k^*\omega_R = \omega_k$.
Moreover $R$ admits a closed 2-form $\eta$ that is exact on each $M_k$ but not on
$R$, witnessing a new cohomology class created by the sum. -/
class IsFinitelyPresented (G : Type*) [Group G] : Prop where
  has_finite_presentation : ∃ (n m : ℕ) (f : FreeGroup (Fin n) →* G),
    Function.Surjective f ∧
    ∃ (rels : Fin m → FreeGroup (Fin n)),
      MonoidHom.ker f = Subgroup.normalClosure (Set.range rels)

/-- The group $G$ is the fundamental group $\pi_1$ of the compact symplectic 4-manifold
$S$: $S$ is finitely presented, admits a compatible almost complex structure, and
there is a group isomorphism $\pi_1(S) \cong G$. -/
class IsFundGroupOfSymplectic4Mfd
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (G : Type*) [Group G] where
  fp : IsFinitelyPresented G
  has_acs : ∃ (J : AlmostComplexStr (inst := inst)), IsCompatibleACS S J
  π₁ : Type*
  grp_π₁ : Group π₁
  iso : @MulEquiv π₁ G grp_π₁.toMul _


