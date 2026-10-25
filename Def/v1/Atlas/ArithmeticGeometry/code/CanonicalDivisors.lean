/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CanonicalDivisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.ArithmeticGeometry.code.CanonicalDivisors


namespace PicardGroup

section PicardGroupDef

variable (Div : Type*) [AddCommGroup Div]

variable (PrincDiv : AddSubgroup Div)

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

end DegreeMap
end PicardGroup
