module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ConductorOrders.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.RingTheory.Conductor
public import Mathlib.NumberTheory.KummerDedekind
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.IntegralClosure
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.Algebra.Module.Lattice
public import Mathlib.Tactic.LinearCombination
public import Def.v1.Atlas.NumberTheoryI.code.ConductorOrders


public section

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
