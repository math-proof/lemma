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
import Def.v1.Atlas.Buildings.code.HeckeAlgebra.Generalized


namespace GeneralizedHecke

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

end GeneralizedHecke
