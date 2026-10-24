/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CrossProductExistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.ModelChains

open Finset BigOperators

namespace AlgebraicTopologyI

noncomputable section

open ContinuousMap

/-- The singular chain cross product
`× : S_p(X) × S_q(Y) → S_{p+q}(X × Y)` as a bilinear map, defined on generators
by applying the universal model cross product to each pair of simplices and
extending freely. This is the underlying construction for Theorem 6.2. -/
noncomputable def crossProductMap (p q : ℕ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] :
    SingularChains p X →+ (SingularChains q Y →+ SingularChains (p + q) (X × Y)) :=
  FreeAbelianGroup.lift (fun (σ : SingularSimplex p X) =>
    FreeAbelianGroup.lift (fun (τ : SingularSimplex q Y) =>
      crossFromModelChain (universalCross p q) σ τ))

/-- Naturality of the cross product: for continuous maps `f : X → X'` and
`g : Y → Y'`, the cross product commutes with the induced maps on singular
chains, i.e. `f_*(a) × g_*(b) = (f × g)_*(a × b)`. This is the naturality
part of Theorem 6.2. -/
structure SingularChainHomotopy {X : Type} {Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f0 f1 : C(X, Y)) where
  hom : ∀ (n : ℕ), SingularChains n X →+ SingularChains (n + 1) Y
  chain_htpy : ∀ (n : ℕ) (s : SingularChains (n + 1) X),
    boundaryMap (n + 1) Y (hom (n + 1) s) + hom n (boundaryMap n X s) =
      SingularChains.map f1 s - SingularChains.map f0 s

/-- The bottom inclusion `X → X × I` given by `x ↦ (x, 0)`. -/
noncomputable def inclusion0 (X : Type) [TopologicalSpace X] :
    C(X, X × ↥I) :=
  ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X ⟨0, unitInterval.zero_mem⟩)

/-- The top inclusion `X → X × I` given by `x ↦ (x, 1)`. -/
noncomputable def inclusion1 (X : Type) [TopologicalSpace X] :
    C(X, X × ↥I) :=
  ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X ⟨1, unitInterval.one_mem⟩)

/-- A natural chain homotopy between the singular-chain maps induced by the
two inclusions `inclusion0, inclusion1 : X → X × I`. The data consists of
homomorphisms `S_n(X) → S_{n+1}(X × I)` satisfying the chain-homotopy
identity and a naturality square in `X`. This is the universal ingredient
used to build chain homotopies from continuous homotopies in Theorem 6.1. -/
structure NaturalChainHomotopyInclusions where
  hom : ∀ (X : Type) [TopologicalSpace X] (n : ℕ),
    SingularChains n X →+ SingularChains (n + 1) (X × ↥I)
  chain_htpy : ∀ (X : Type) [TopologicalSpace X] (n : ℕ)
    (s : SingularChains (n + 1) X),
    boundaryMap (n + 1) (X × ↥I) (hom X (n + 1) s) + hom X n (boundaryMap n X s) =
      SingularChains.map (inclusion1 X) s - SingularChains.map (inclusion0 X) s
  naturality : ∀ (X X' : Type) [TopologicalSpace X] [TopologicalSpace X']
    (g : C(X', X)) (n : ℕ) (s : SingularChains n X'),
    SingularChains.map (ContinuousMap.prodMap g (ContinuousMap.id ↥I)) (hom X' n s) =
      hom X n (SingularChains.map g s)

/-- The fundamental singular `1`-simplex `ι₁ : Δ¹ → I` given on barycentric
coordinates `(t₀, t₁)` by `(t₀, t₁) ↦ t₁`. -/
noncomputable def iotaSimplex : SingularSimplex 1 ↥I where
  toFun t := ⟨t.1 1, by
    obtain ⟨hnn, hsum⟩ := t.2
    constructor
    · exact hnn 1
    · have h0 := hnn 0
      have : t.1 0 + t.1 1 = 1 := by
        have := hsum
        simp [Fin.sum_univ_two] at this
        exact this
      linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_apply 1).comp continuous_subtype_val
