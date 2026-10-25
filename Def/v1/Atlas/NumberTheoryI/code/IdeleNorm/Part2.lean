/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdeleNorm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.Ideles.Part3
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Ideles
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Theorem.v1.Atlas.NumberTheoryI.code.IdeleNorm


noncomputable section

open NumberField IsDedekindDomain Ideles

def HeightOneSpectrum.placesAbove {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (v : HeightOneSpectrum (𝓞 K)) : Finset (HeightOneSpectrum (𝓞 L)) :=
  (HeightOneSpectrum.finite_placesAbove v).toFinset

end
