/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TorsorIffJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.WeilChatelet.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.WeilChatelet
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.JInvariant
import Def.v1.Atlas.ArithmeticGeometry.code.JInvariant.Part3
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Structure.v1.Atlas.ArithmeticGeometry.code.TorsorIffJacobian
set_option autoImplicit false


noncomputable section

universe u

/-- A Galois action is *equivariant* for the torsor structure if it commutes with $+_v$:
$\sigma(g +_v c) = \sigma(g) +_v \sigma(c)$ for all $\sigma, g, c$. -/
def GaloisAction.IsEquivariant {G : Type u} [Group G] {E_pts : Type u} [AddCommGroup E_pts]
    {C_pts : Type u} [AddTorsor E_pts C_pts] (ga : GaloisAction G E_pts C_pts) : Prop :=
  ∀ (σ : G) (g : E_pts) (c : C_pts),
    ga.actC σ (g +ᵥ c) = (ga.actE σ g) +ᵥ (ga.actC σ c)

/-- A bijection $\varphi \colon C \to E$ is *Galois compatible* with respect to $\mathrm{ga}$ if
for every $\sigma$ there exists $P_\sigma \in E$ such that
$\sigma(\varphi Q) = \varphi(\sigma Q) + P_\sigma$ for all $Q$; this expresses that $\varphi$
differs from a Galois-equivariant map by a cocycle. -/
def IsGaloisCompatible {G : Type u} [Group G] {E_pts : Type u} [AddCommGroup E_pts]
    {C_pts : Type u} (ga : GaloisAction G E_pts C_pts) (φ : C_pts ≃ E_pts) : Prop :=
  ∀ σ : G, ∃ P_σ : E_pts, ∀ Q : C_pts,
    (ga.actE σ) (φ Q) = φ ((ga.actC σ) Q) + P_σ

/-- $W$ is a Jacobian of $C$ over $k$ if $C$ is a genus-one curve and there exists a Galois action
together with a Galois-compatible bijection $\varphi \colon C \to E(W)$. -/
def IsJacobianOf (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (C_pts : Type u) : Prop :=
  IsGenusOneCurvePoints k C_pts ∧
  ∃ (ga : GaloisAction (AbsGaloisGroup k) E_pts C_pts)
    (φ : C_pts ≃ E_pts), IsGaloisCompatible ga φ

end
