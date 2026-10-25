/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CurveTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ArithmeticGeometry.code.MorphismsCurves
import Abbrev.v1.Atlas.ArithmeticGeometry.code.RegularLocalRings
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RegularLocalRings
import Def.v1.Atlas.ArithmeticGeometry.code.CurveTheory.Part3


noncomputable section

open Module IsDiscreteValuationRing

namespace ArithmeticGeometry

section DVRNormalization

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

structure SmoothProjectiveCurveData (k : Type u) [Field k] (K : Type u) [Field K]
    [Algebra k K] (n : ℕ) where
  P : Type u
  R : P → Type u
  [instCR : ∀ p, CommRing (R p)]
  [instID : ∀ p, IsDomain (R p)]
  [instDVR : ∀ p, IsDiscreteValuationRing (R p)]
  [instAlg : ∀ p, Algebra (R p) K]
  [instFR : ∀ p, IsFractionRing (R p) K]
  [instAlgKR : ∀ p, Algebra k (R p)]
  [instScalarTower : ∀ p, IsScalarTower k (R p) K]
  emb : Fin (n + 1) → K
  emb_ne_zero : ∃ i, emb i ≠ 0
  n_pos : n ≥ 1
  emb_injective : Function.Injective emb
  point_nonempty : Nonempty P
  localRing_injective : ∀ (p₁ p₂ : P),
    (algebraMap (R p₁) K).range = (algebraMap (R p₂) K).range → p₁ = p₂
  localRing_surjective : ∀ (V : ValuationSubring K)
    [IsDiscreteValuationRing V] [IsFractionRing V K],
    ∃ p, (algebraMap (R p) K).range = V.toSubring

end DVRNormalization
end ArithmeticGeometry
end
