/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WCGroupH1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.WeilChatelet
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.WeilChatelet
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.GaloisCohomology
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology

noncomputable section

universe u

open GaloisCohomology

/-- Data witnessing the bijection between the Weil-Châtelet set of $E$-torsors over $k$ (mod
$k$-isomorphism) and the first cohomology group $H^1(G, E_{\mathrm{pts}})$: a well-defined,
injective, and surjective `cocycleMap`. -/
structure WCH1Data (k : Type u) [Field k] (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousNeg E_pts] [ContinuousSMul G E_pts] where
  cocycleMap : ETorsor k W E_pts → H1 G E_pts
  cocycleMap_wellDefined : ∀ (T₁ T₂ : ETorsor k W E_pts),
    ETorsor.Equiv T₁ T₂ → cocycleMap T₁ = cocycleMap T₂
  cocycleMap_injective : ∀ (T₁ T₂ : ETorsor k W E_pts),
    cocycleMap T₁ = cocycleMap T₂ → ETorsor.Equiv T₁ T₂
  cocycleMap_surjective : Function.Surjective cocycleMap

/-- Data of a Galois action on a torsor `T`: a Galois map $\sigma \mapsto \sigma_C$ acting on
points of `T`, equivariant with the $E$-action and a group homomorphism in $\sigma$, together
with a continuity condition. -/
structure GaloisActionOnTorsor (k : Type u) [Field k] (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousSMul G E_pts]
    (T : ETorsor k W E_pts) where
  σ_C : G → T.C_pts → T.C_pts
  compat : haveI := T.torsor.toAddTorsor
    ∀ (σ : G) (p : E_pts) (c : T.C_pts), σ_C σ (p +ᵥ c) = (σ • p) +ᵥ σ_C σ c
  mul_compat : ∀ (τ σ : G) (c : T.C_pts), σ_C (τ * σ) c = σ_C τ (σ_C σ c)
  cont : haveI := T.torsor.toAddTorsor
    ∀ (Q₀ : T.C_pts), Continuous (fun σ => σ_C σ Q₀ -ᵥ Q₀ : G → E_pts)

/-- Explicit bijection $\mathrm{WC}(E/k) \simeq H^1(G, E_{\mathrm{pts}})$ given a choice of
`WCH1Data`. -/
noncomputable def wc_h1_setEquiv {k : Type u} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
    {E_pts : Type u} [AddCommGroup E_pts]
    {G : Type u} [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousNeg E_pts] [ContinuousSMul G E_pts]
    (data : WCH1Data k W E_pts G) :
    WC k W E_pts ≃ H1 G E_pts := by
  have hwd : ∀ (T₁ T₂ : ETorsor k W E_pts),
      T₁ ≈ T₂ → data.cocycleMap T₁ = data.cocycleMap T₂ :=
    data.cocycleMap_wellDefined
  let f : WC k W E_pts → H1 G E_pts :=
    Quotient.lift data.cocycleMap hwd
  have hbij : Function.Bijective f := by
    constructor
    · intro a b hab
      induction a using Quotient.ind
      induction b using Quotient.ind
      exact Quotient.sound (data.cocycleMap_injective _ _ hab)
    · intro h
      obtain ⟨T, hT⟩ := data.cocycleMap_surjective h
      exact ⟨Quotient.mk _ T, hT⟩
  exact Equiv.ofBijective f hbij

/-- Transport the abelian group structure on $H^1$ to `WC` via the bijection of
`wc_h1_setEquiv`, making `WC k W E_pts` into an `AddCommGroup`. -/
@[reducible] noncomputable def WC.addCommGroupOfData {k : Type u} [Field k]
    {W : WeierstrassCurve k} [W.IsElliptic]
    {E_pts : Type u} [AddCommGroup E_pts]
    {G : Type u} [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousNeg E_pts] [ContinuousSMul G E_pts]
    (data : WCH1Data k W E_pts G) :
    AddCommGroup (WC k W E_pts) :=
  (wc_h1_setEquiv data).addCommGroup

/-- The Weil-Châtelet group is isomorphic, as an additive group, to $H^1(G, E_{\mathrm{pts}})$,
once we transport the group structure via the bijection of `wc_h1_setEquiv`. -/
noncomputable def wc_h1_equiv {k : Type u} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
    {E_pts : Type u} [AddCommGroup E_pts]
    {G : Type u} [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousNeg E_pts] [ContinuousSMul G E_pts]
    (data : WCH1Data k W E_pts G) :
    letI := WC.addCommGroupOfData data
    WC k W E_pts ≃+ H1 G E_pts :=
  letI := WC.addCommGroupOfData data
  (wc_h1_setEquiv data).addEquiv
