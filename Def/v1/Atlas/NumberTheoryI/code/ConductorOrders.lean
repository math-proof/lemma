/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ConductorOrders.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

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

@[expose] public section

noncomputable section

open Ideal Polynomial Algebra IsDedekindDomain nonZeroDivisors

section ConductorDef

variable (R : Type*) (S : Type*) [CommRing R] [CommRing S] [Algebra R S]

def Subalgebra.conductorIdeal (A : Subalgebra R S) : Ideal S where
  carrier := {a : S | ∀ b : S, a * b ∈ A}
  zero_mem' b := by simp [A.zero_mem]
  add_mem' {a₁ a₂} ha₁ ha₂ b := by rw [add_mul]; exact A.add_mem (ha₁ b) (ha₂ b)
  smul_mem' c a ha b := by
    simp only [smul_eq_mul, Set.mem_setOf_eq] at *
    rw [show c * a * b = a * (c * b) by ring]
    exact ha (c * b)

end ConductorDef
end
