/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Instance.v1.Atlas.NumberTheoryI.code.LocalizationDedekind
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.LocalizationDedekind
import Class.v1.Atlas.NumberTheoryI.code.DedekindProperties
open Ideal UniqueFactorizationMonoid


omit [IsDomain A'] in

noncomputable example : Semifield (FractionalIdeal A'⁰ K') := inferInstance

