/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CyclotomicRamification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Cor1015
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Cor1015
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.LocalExtensions
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.TracePairing
import sympy.atlas.v1.Atlas.NumberTheoryI.code.LocalExtensions
import sympy.atlas.v1.Atlas.NumberTheoryI.code.TracePairing

noncomputable section
