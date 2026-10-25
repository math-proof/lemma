/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.CompatibleComplexStructures
import Theorem.v1.Atlas.GeometryOfManifolds.code.CompatibleComplexStructures
import Class.v1.Atlas.GeometryOfManifolds.code.TangentBundleDFS
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Class.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds
set_option autoImplicit false

open DifferentialFormSpace SymplecticLinearAlgebra


/-- An **almost complex structure** on the vector field space $VF$: an endomorphism
$J : VF \to VF$ satisfying $J^2 = -\mathrm{id}$ (expressed dually as
$\iota_{J(JX)} \alpha = -\iota_X \alpha$ on all $1$-forms $\alpha$). -/
structure AlmostComplexStr
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  J : VF → VF
  sq_neg_id : ∀ (X : VF) (α : Ω 1), inst.ι (J (J X)) α = -(inst.ι X α)


/-- $J$ is **compatible** with the symplectic form $\omega$: $\omega(Ju, Jv) = \omega(u, v)$
(preservation) and the taming map $v \mapsto \omega(Jv, \cdot)$ is injective. -/
structure IsCompatibleACS
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst)) : Prop where
  preserves : ∀ (u v : VF),
    inst.ι (J.J u) (inst.ι (J.J v) S.ω) = inst.ι u (inst.ι v S.ω)
  taming : Function.Injective (fun (v : VF) => inst.ι (J.J v) S.ω)


/-- $J$ **tames** $\omega$: for any $X \neq Y$, $\omega(JX, \iota_X \omega - \iota_Y \omega)$ is
positive, expressing a strict positivity condition $\omega(\cdot, J\cdot) > 0$. -/
structure IsTaming
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hp : HasPositivity (Ω 0)]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst)) : Prop where
  taming : ∀ (X Y : VF), X ≠ Y →
    hp.IsPositive (inst.ι (J.J X) (inst.ι X S.ω - inst.ι Y S.ω))


/-- A **compatible triple** $(\omega, J, g)$ on a symplectic manifold: a compatible almost
complex structure $J$ together with the induced Riemannian metric $g(\cdot, \cdot) = \omega(\cdot, J\cdot)$. -/
structure CompatibleTriple
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) where
  J : AlmostComplexStr (inst := inst)
  compat : IsCompatibleACS S J
  g : Ω 2


