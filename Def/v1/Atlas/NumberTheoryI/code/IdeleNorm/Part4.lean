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
import Theorem.v1.Atlas.NumberTheoryI.code.IdeleNorm.Part3


noncomputable section

open NumberField IsDedekindDomain Ideles

def finiteAdeleNormHom (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    FiniteAdeleRing (𝓞 L) L →* FiniteAdeleRing (𝓞 K) K where
  toFun b := ⟨fun v => finiteNormComponent K L v b,
    finiteNormComponent_mem_integers_almost_all K L b⟩
  map_one' := Subtype.ext <| funext fun v => (finiteNormComponent K L v).map_one
  map_mul' b₁ b₂ := Subtype.ext <| funext fun v => (finiteNormComponent K L v).map_mul b₁ b₂

def adeleNormHom (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    NumberField.AdeleRing (𝓞 L) L →* NumberField.AdeleRing (𝓞 K) K :=
  MonoidHom.prodMap (infiniteAdeleNormHom K L) (finiteAdeleNormHom K L)

def ideleNorm (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    IdeleGroup L →* IdeleGroup K :=
  Units.map (adeleNormHom K L)

end
