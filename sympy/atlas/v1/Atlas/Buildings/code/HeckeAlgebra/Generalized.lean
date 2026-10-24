/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generalized.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic

namespace GeneralizedHecke

/-- Data of a generalized BN-pair on a group `G`: subgroups recording the label-preserving
subgroup, Borel, normalizer $N$, restricted normalizer $N ∩$ labelPreserving, the torus
$N ∩ B$, and the restricted torus, together with their intersection axioms. -/
structure GeneralizedBNPairData (G : Type*) [Group G] where
  labelPreserving : Subgroup G
  borel : Subgroup G
  normalizerN : Subgroup G
  normalizerRestricted : Subgroup G
  torus : Subgroup G
  torusRestricted : Subgroup G
  borel_in_labelPreserving : borel ≤ labelPreserving
  normalizerRestricted_eq : normalizerRestricted = normalizerN ⊓ labelPreserving
  torus_eq : torus = normalizerN ⊓ borel
  torusRestricted_eq : torusRestricted = normalizerRestricted ⊓ borel

/-- Property: the Borel sits inside the label-preserving subgroup. -/
def GeneralizedBNPairData.BorelInLabelPreserving {G : Type*} [Group G]
    (d : GeneralizedBNPairData G) : Prop :=
  d.borel ≤ d.labelPreserving

/-- Property: the restricted normalizer is exactly the intersection of $N$ with the
label-preserving subgroup. -/
def GeneralizedBNPairData.NormalizerRestrictedIsIntersection {G : Type*} [Group G]
    (d : GeneralizedBNPairData G) : Prop :=
  ∀ g : G, g ∈ d.normalizerRestricted ↔ g ∈ d.normalizerN ∧ g ∈ d.labelPreserving

/-- Property: the torus $T = N ∩ B$. -/
def GeneralizedBNPairData.TorusIsIntersection {G : Type*} [Group G]
    (d : GeneralizedBNPairData G) : Prop :=
  ∀ g : G, g ∈ d.torus ↔ g ∈ d.normalizerN ∧ g ∈ d.borel

/-- Property: the restricted torus equals $N_{\text{res}} ∩ B$. -/
def GeneralizedBNPairData.TorusRestrictedIsIntersection {G : Type*} [Group G]
    (d : GeneralizedBNPairData G) : Prop :=
  ∀ g : G, g ∈ d.torusRestricted ↔ g ∈ d.normalizerRestricted ∧ g ∈ d.borel

/-- A function $f : G → R$ is $B$-bi-invariant if $f(b_1 g b_2) = f(g)$ for all
$b_1, b_2 ∈ B$ and all $g ∈ G$. -/
def BiInvariantFunction {G R : Type*} [Group G] (B : Subgroup G) (f : G → R) : Prop :=
  ∀ (b₁ b₂ : G), b₁ ∈ B → b₂ ∈ B → ∀ g, f (b₁ * g * b₂) = f g

/-- Abstract data of a Hecke algebra associated to a Borel subgroup $B ⊆ G$: an $R$-module
`carrier` with a convolution product making it into an $R$-algebra. -/
structure HeckeAlgebraData (G R : Type*) [Group G] [CommRing R] where
  borel : Subgroup G
  carrier : Type*
  add : carrier → carrier → carrier
  zero : carrier
  smul : R → carrier → carrier
  convolution : carrier → carrier → carrier
  one : carrier
  conv_assoc : ∀ f g h : carrier, convolution (convolution f g) h = convolution f (convolution g h)
  one_conv : ∀ f : carrier, convolution one f = f
  conv_one : ∀ f : carrier, convolution f one = f
  conv_add : ∀ f g h : carrier, convolution f (add g h) = add (convolution f g) (convolution f h)
  add_conv : ∀ f g h : carrier, convolution (add f g) h = add (convolution f h) (convolution g h)
  smul_conv : ∀ (r : R) (f g : carrier), convolution (smul r f) g = smul r (convolution f g)

/-- The quotient datum $Ω = T / T_{\text{res}}$ as a chain of subgroup inclusions. -/
structure OmegaQuotient (G : Type*) [Group G] where
  torus : Subgroup G
  torusRestricted : Subgroup G
  le : torusRestricted ≤ torus

/-- Abstract semidirect-product decomposition data for $N$ inside $G$ as a product of
$W$ and $Ω$, with chosen projections to each factor. -/
structure SemidirectDecomposition (G W Ω : Type*) [Group G] [Group W] [Group Ω] where
  normalizerN : Subgroup G
  torusRestricted : Subgroup G
  le : torusRestricted ≤ normalizerN
  projW : G → W
  projΩ : G → Ω

/-- Data of a convolution embedding $Ω → H$ into a $k$-algebra: the character map
`ch` is a $k$-linearly independent monoid homomorphism. -/
structure OmegaConvolutionData (k : Type u) [CommRing k]
    (Ω : Type u) [Group Ω] where
  H : Type u
  [ringH : Ring H]
  [algH : Algebra k H]
  ch : Ω → H
  ch_mul : ∀ σ τ : Ω, ch σ * ch τ = ch (σ * τ)
  ch_one : ch 1 = (1 : H)
  ch_linearIndependent : LinearIndependent k ch

attribute [instance] OmegaConvolutionData.algH OmegaConvolutionData.ringH

namespace OmegaConvolutionData

variable {k : Type u} [CommRing k] {Ω : Type u} [Group Ω]
variable (d : OmegaConvolutionData k Ω)

/-- Packages `ch : Ω → H` as a monoid homomorphism. -/
def chMonoidHom : Ω →* d.H where
  toFun := d.ch
  map_one' := d.ch_one
  map_mul' σ τ := by rw [d.ch_mul]

/-- The induced $k$-algebra homomorphism $k[Ω] → H$ extending `chMonoidHom`. -/
def algHomToH : MonoidAlgebra k Ω →ₐ[k] d.H :=
  MonoidAlgebra.lift k d.H Ω d.chMonoidHom

/-- The proposition that $k[Ω] ≃ₐ H_Ω$, the subalgebra of $H$ generated by the image of $Ω$. -/
def proposition_HOmega_iso_groupAlgebra :
    MonoidAlgebra k Ω ≃ₐ[k] d.algHomToH.range :=
  AlgEquiv.ofInjective d.algHomToH d.algHomToH_injective

end OmegaConvolutionData

/-- Convolution identities relating the $Ω$-characters, $W$-characters, and the joint
characters in a generalized Hecke algebra, including the conjugation action `omegaConj`. -/
structure HeckeConvolutionIdentities (k : Type u) [CommRing k]
    (Ω : Type u) [Group Ω] (W : Type u) [Group W] where
  H : Type u
  [ringH : Ring H]
  [algH : Algebra k H]
  ch_omega : Ω → H
  ch_weyl : W → H
  ch_full : Ω → W → H
  omegaConj : Ω → W → W
  conv_left : ∀ (σ : Ω) (w : W), ch_omega σ * ch_weyl w = ch_full σ w
  conv_right : ∀ (w : W) (σ : Ω),
    ch_weyl w * ch_omega σ = ch_full σ (omegaConj σ w)

attribute [instance] HeckeConvolutionIdentities.algH HeckeConvolutionIdentities.ringH

namespace HeckeConvolutionIdentities

variable {k : Type u} [CommRing k] {Ω : Type u} [Group Ω] {W : Type u} [Group W]
variable (d : HeckeConvolutionIdentities k Ω W)
