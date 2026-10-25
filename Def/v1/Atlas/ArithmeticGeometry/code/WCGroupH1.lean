/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WCGroupH1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.WeilChatelet.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.WeilChatelet
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.GaloisCohomology
import Abbrev.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part3
import Structure.v1.Atlas.ArithmeticGeometry.code.WCGroupH1


noncomputable section

universe u

open GaloisCohomology

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

end
