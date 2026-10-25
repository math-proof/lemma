/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CanonicalDivisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.ArithmeticGeometry.code.CanonicalDivisors


namespace PicardGroup

section DegreeMap

variable {Div : Type*} [AddCommGroup Div]

variable {PrincDiv : AddSubgroup Div}

variable (deg : Div →+ ℤ)

variable (hdeg : PrincDiv ≤ deg.ker)

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

end DegreeMap
end PicardGroup
