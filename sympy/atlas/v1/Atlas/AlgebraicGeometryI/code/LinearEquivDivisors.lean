/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

noncomputable section

open scoped nonZeroDivisors

namespace LinearEquivDivisors


/-- The group of Weil divisors on `Y` as finitely supported functions `Y → ℤ`. -/
abbrev WeilDivisorGroup (Y : Type*) := Y →₀ ℤ

/-- A Weil divisor `D` is effective iff all of its coefficients are nonnegative. -/
def WeilDivisor.IsEffective {Y : Type*} (D : WeilDivisorGroup Y) : Prop :=
  ∀ y : Y, 0 ≤ D y

/-- Two Cartier divisors (nonzero ideals of a Dedekind domain) are linearly
equivalent iff they represent the same element of the class group. -/
def CartierDivisor.LinearlyEquivalent (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] (I J : (Ideal A)⁰) : Prop :=
  ClassGroup.mk0 I = ClassGroup.mk0 J


variable {Y : Type*}

/-- The subgroup of principal Weil divisors inside the full Weil divisor group. -/
abbrev PrincipalDivisors (Y : Type*) := AddSubgroup (WeilDivisorGroup Y)

/-- Linear equivalence of Weil divisors modulo a chosen subgroup `P` of principal
divisors: `D₁ ~ D₂` iff `D₁ - D₂ ∈ P` (Def 32, Lec 16). -/
def WeilLinearlyEquivalent (P : PrincipalDivisors Y) (D₁ D₂ : WeilDivisorGroup Y) :
    Prop :=
  D₁ - D₂ ∈ P


/-- Linear equivalence of Weil divisors is an equivalence relation. -/
theorem weilLinearlyEquivalent_equivalence (P : PrincipalDivisors Y) :
    Equivalence (WeilLinearlyEquivalent P) where
  refl D := by
    show D - D ∈ P
    simp [P.zero_mem]
  symm {a b} h := by
    show b - a ∈ P
    have : b - a = -(a - b) := by abel
    rw [this]
    exact P.neg_mem h
  trans {a b c} h1 h2 := by
    show a - c ∈ P
    have : a - c = (a - b) + (b - c) := by abel
    rw [this]
    exact P.add_mem h1 h2

/-- Linear equivalence of Weil divisors is reflexive. -/
theorem WeilLinearlyEquivalent.refl (P : PrincipalDivisors Y)
    (D : WeilDivisorGroup Y) :
    WeilLinearlyEquivalent P D D :=
  (weilLinearlyEquivalent_equivalence P).refl D

/-- Linear equivalence of Weil divisors is symmetric. -/
theorem WeilLinearlyEquivalent.symm (P : PrincipalDivisors Y)
    {D₁ D₂ : WeilDivisorGroup Y} (h : WeilLinearlyEquivalent P D₁ D₂) :
    WeilLinearlyEquivalent P D₂ D₁ :=
  (weilLinearlyEquivalent_equivalence P).symm h

/-- Linear equivalence of Weil divisors is transitive. -/
theorem WeilLinearlyEquivalent.trans (P : PrincipalDivisors Y)
    {D₁ D₂ D₃ : WeilDivisorGroup Y}
    (h₁ : WeilLinearlyEquivalent P D₁ D₂) (h₂ : WeilLinearlyEquivalent P D₂ D₃) :
    WeilLinearlyEquivalent P D₁ D₃ :=
  (weilLinearlyEquivalent_equivalence P).trans h₁ h₂

/-- The setoid on Weil divisors given by linear equivalence relative to `P`. -/
def weilLinearEquivSetoid (P : PrincipalDivisors Y) :
    Setoid (WeilDivisorGroup Y) :=
  ⟨WeilLinearlyEquivalent P, weilLinearlyEquivalent_equivalence P⟩


/-- The degree of a Weil divisor is the sum of its coefficients. -/
def WeilDivisor.degree (D : WeilDivisorGroup Y) : ℤ :=
  D.sum (fun _ n => n)


/-- The complete linear system `|D|`: all effective Weil divisors linearly
equivalent to `D`. -/
def completeLinearSystem (P : PrincipalDivisors Y) (D : WeilDivisorGroup Y) :
    Set (WeilDivisorGroup Y) :=
  {D' | WeilDivisor.IsEffective D' ∧ WeilLinearlyEquivalent P D' D}


/-- Dimension of a complete linear system, defined as `dim_k V - 1` where `V`
is the global sections module. -/
def completeLinearSystemDim (k : Type*) [Field k] (V : Type*)
    [AddCommGroup V] [Module k V] [Module.Finite k V] : ℤ :=
  (Module.finrank k V : ℤ) - 1
