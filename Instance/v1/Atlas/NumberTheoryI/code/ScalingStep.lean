/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ScalingStep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Instance.v1.Atlas.NumberTheoryI.code.HenselLemmas
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Localization.FractionRing
@[expose] public section

open Polynomial IsLocalRing


noncomputable instance dvr_normalizedGCDMonoid
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    NormalizedGCDMonoid A :=
  (inferInstance : Nonempty (NormalizedGCDMonoid A)).some

