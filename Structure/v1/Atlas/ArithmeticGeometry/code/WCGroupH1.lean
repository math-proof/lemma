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

end
