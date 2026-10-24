/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TorsorIffJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.WeilChatelet
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.WeilChatelet
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.JInvariant
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.JInvariant
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false

noncomputable section

universe u

/-- The *absolute Galois group* $\mathrm{Gal}(\bar k / k)$ of a field $k$: ring automorphisms of an
algebraic closure of $k$. -/
abbrev AbsGaloisGroup (k : Type u) [Field k] : Type u :=
  AlgebraicClosure k ≃+* AlgebraicClosure k

/-- The absolute Galois group `AbsGaloisGroup k` is a group under composition. -/
noncomputable instance AbsGaloisGroup.instGroup (k : Type u) [Field k] :
    Group (AbsGaloisGroup k) :=
  inferInstance

/-- A `GaloisAction G E_pts C_pts` packages an action of the group $G$ on both the elliptic curve
points $E$ (as additive equivalences) and on a torsor candidate $C$ (as set equivalences). -/
structure GaloisAction (G : Type u) [Group G] (E_pts : Type u) [AddCommGroup E_pts]
    (C_pts : Type u) where
  actE : G → E_pts ≃+ E_pts
  actC : G → C_pts ≃ C_pts

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

/-- Galois descent: every genus-one curve $C$ over $k$ has a Jacobian Weierstrass model $W/k$,
together with a Galois action on $E(W)$ and a Galois-compatible bijection $C \to E(W)$. -/
variable {k : Type u} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {E_pts : Type u} [AddCommGroup E_pts] {C_pts : Type u}


/-- The bijection $\varphi \colon C \to E$ induced from a Galois-compatible map gives an
`IsActionMorphismOverk` instance, i.e. the resulting $E$-action on $C$ is a $k$-morphism. -/
theorem isActionMorphismOverk_of_galoisCompat
    (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (C_pts : Type u) [hne : Nonempty C_pts]
    (φ : C_pts ≃ E_pts) :
    @IsActionMorphismOverk _ _ W _ E_pts _ C_pts (addTorsorOfEquiv E_pts C_pts φ) :=
  IsActionMorphismOverk.ofEquiv k W E_pts C_pts φ

/-- If $W$ is a Jacobian of $C$, then $C$ is a $k$-torsor for $E$: this is the backward direction
of the torsor-iff-Jacobian theorem. -/
def isJacobianOf_imp_isETorsor
    (hJ : IsJacobianOf k W E_pts C_pts) :
    IsETorsor k W E_pts C_pts := by
  have hg := hJ.1


  let hexists := hJ.2

  let φ : C_pts ≃ E_pts :=
    hexists.choose_spec.choose

  have hne : Nonempty C_pts := ⟨φ.symm 0⟩
  exact
  { toAddTorsor := addTorsorOfEquiv E_pts C_pts φ
    genusOne := hg
    actionMorphism := isActionMorphismOverk_of_galoisCompat k W E_pts C_pts φ }
