/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generalized.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Def.v1.Atlas.Buildings.code.HeckeAlgebra.Generalized.Part2


public section

namespace GeneralizedHecke

attribute [instance] OmegaConvolutionData.algH OmegaConvolutionData.ringH

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

end GeneralizedHecke
