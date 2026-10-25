/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ScalingStep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.NumberTheoryI.code.HenselLemmas
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.HenselLemmas
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Localization.FractionRing
open Polynomial IsLocalRing


noncomputable instance dvr_normalizedGCDMonoid
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    NormalizedGCDMonoid A :=
  (inferInstance : Nonempty (NormalizedGCDMonoid A)).some

