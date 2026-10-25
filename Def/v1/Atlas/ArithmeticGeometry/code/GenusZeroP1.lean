/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GenusZeroP1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.GenusOnePlaneCubic
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.GenusOnePlaneCubic


noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

/-- The projective line $\mathbb{P}^1_k$ packaged as a `SmoothProjectiveCurveOverField k`. We
realize $\mathbb{P}^1_k$ via $\mathrm{Spec}\,k[X]$ together with its structure morphism, equipped
with the proofs that it is integral, has Krull dimension $1$, is nonempty, and has genus $0$. -/
def projectiveLineAsCurve (k : Type*) [Field k] :
    SmoothProjectiveCurveOverField k :=


  { toScheme := Spec (CommRingCat.of (Polynomial k))
    isIntegral := instIsIntegralSpecOfIsDomainCarrier
    krullDim_eq := by
      change topologicalKrullDim (PrimeSpectrum (Polynomial k)) = 1
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
          Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
      norm_num
    nonempty := instNonemptyCarrierCarrierCommRingCatSpecOfNontrivialCarrier
    structureMorphism := Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
    genusVal := 0 }

/-- The property of being $k$-isomorphic to the projective line $\mathbb{P}^1_k$, compatibly with
the structure morphism. -/
def SmoothProjectiveCurveOverField.IsIsomorphicToP1 {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k) : Prop :=
  ∃ (φ : C.toScheme ≅ (projectiveLineAsCurve k).toScheme),
    φ.hom ≫ (projectiveLineAsCurve k).structureMorphism = C.structureMorphism

end
