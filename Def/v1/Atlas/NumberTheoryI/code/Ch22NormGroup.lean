/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part28
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.RayClassFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.ValuationBijection
import Theorem.v1.Atlas.NumberTheoryI.code.ValuationBijection


noncomputable section

open scoped NumberField

open Classical

namespace RayClassField

universe u

def lyingUnder (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
  IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝔮

def ramificationIndex' (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) : ℕ :=
  Ideal.ramificationIdx (lyingUnder K L 𝔮).asIdeal 𝔮.asIdeal

def inertiaDegree' (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) : ℕ :=
  Ideal.inertiaDeg (lyingUnder K L 𝔮).asIdeal 𝔮.asIdeal

end RayClassField
end
