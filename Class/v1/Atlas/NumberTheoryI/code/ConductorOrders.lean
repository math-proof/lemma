/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ConductorOrders.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Conductor
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.Algebra.Module.Lattice
import Mathlib.Tactic.LinearCombination
import Def.v1.Atlas.NumberTheoryI.code.ConductorOrders


noncomputable section

open Ideal Polynomial Algebra IsDedekindDomain nonZeroDivisors

section OrderDef

class IsOrder (O : Type*) [CommRing O] [IsDomain O] : Prop where
  isNoetherian : IsNoetherianRing O
  dimLEOne : Ring.DimensionLEOne O
  notIsField : ¬ IsField O
  intClosureFG : ∀ (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K],
    Module.Finite O (integralClosure O K)

class IsAOrder (A : Type*) (L : Type*) [CommRing A] [CommRing L] [Algebra A L]
    (O : Subalgebra A L) : Prop where
  fg : (O.toSubmodule).FG
  spans : ∀ (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [IsScalarTower A K L],
    Submodule.span K (Set.range (Subtype.val : O → L)) = ⊤

end OrderDef
end
