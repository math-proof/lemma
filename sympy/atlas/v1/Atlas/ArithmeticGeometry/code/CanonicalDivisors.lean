/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CanonicalDivisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace PicardGroup

section PicardGroupDef


variable (Div : Type*) [AddCommGroup Div]
variable (PrincDiv : AddSubgroup Div)

abbrev PicGrp := Div ⧸ PrincDiv

def toPic : Div →+ PicGrp Div PrincDiv :=
  QuotientAddGroup.mk' PrincDiv

def LinearlyEquivalent (D₁ D₂ : Div) : Prop :=
  D₁ - D₂ ∈ PrincDiv


end PicardGroupDef

section DegreeMap

variable {Div : Type*} [AddCommGroup Div]
variable {PrincDiv : AddSubgroup Div}

variable (deg : Div →+ ℤ)

variable (hdeg : PrincDiv ≤ deg.ker)

def degPic : PicGrp Div PrincDiv →+ ℤ :=
  QuotientAddGroup.lift PrincDiv deg hdeg

def Pic0 : AddSubgroup (PicGrp Div PrincDiv) :=
  (degPic deg hdeg).ker

def IsMaximalDivisorFor [PartialOrder Div] (ω : Ω) (D : Div) : Prop :=
  omegaD ω D ∧ ∀ D' : Div, omegaD ω D' → D' ≤ D

omit [AddCommGroup Div] in

structure IsDivOmegaMaximal [PartialOrder Div] (ω : Ω) : Prop where
  mem : omegaD ω (divΩ ω)
  le_divΩ : ∀ D : Div, omegaD ω D → D ≤ divΩ ω

omit [AddCommGroup Div] [Zero Ω] in

def div_differential (ω : Ω) : Div := divΩ ω

def IsCanonical (D : Div) : Prop :=
  ∃ ω : Ω, ω ≠ 0 ∧ D = divΩ ω

def ordOmega (P : Place) (ω : Ω) : ℤ := ordP P (divΩ ω)

section APILemmas

variable {Div : Type*} {Ω : Type*} {Place : Type*}
variable {divΩ : Ω → Div} {ordP : Place → Div → ℤ}


end APILemmas

def LinearlyEquivalent (D₁ D₂ : Div) : Prop :=
  ∃ f : F, f ≠ 0 ∧ D₂ = D₁ + divF f
