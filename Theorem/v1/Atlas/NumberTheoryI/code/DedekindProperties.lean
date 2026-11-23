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
public import Class.v1.Atlas.NumberTheoryI.code.DedekindProperties
open Ideal UniqueFactorizationMonoid

public section

omit [IsDomain A'] in

noncomputable example : Semifield (FractionalIdeal A'⁰ K') := inferInstance

