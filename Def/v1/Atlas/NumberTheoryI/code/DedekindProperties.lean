/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Instance.v1.Atlas.NumberTheoryI.code.LocalizationDedekind
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.LocalizationDedekind
public import Theorem.v1.Atlas.NumberTheoryI.code.DedekindProperties

@[expose] public section

open Ideal UniqueFactorizationMonoid


section DedekindQuotientPIR

set_option maxHeartbeats 800000

def localizeAtPrime
    {A : Type*} [CommRing A] [IsDomain A]
    (𝔪 : Ideal A) [𝔪.IsPrime]
    (I : FractionalIdeal A⁰ (FractionRing A)) :
    FractionalIdeal (Localization.AtPrime 𝔪)⁰ (FractionRing A) :=
  I.extended (FractionRing A)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (FaithfulSMul.algebraMap_injective A _))

def IsLocallyPrincipal
    {A : Type*} [CommRing A] [IsDomain A]
    (I : FractionalIdeal A⁰ (FractionRing A)) : Prop :=
  ∀ (𝔪 : Ideal A) [𝔪.IsMaximal],
    ((I.localizeAtPrime 𝔪 :
      Submodule (Localization.AtPrime 𝔪) (FractionRing A)).IsPrincipal)

end DedekindQuotientPIR
