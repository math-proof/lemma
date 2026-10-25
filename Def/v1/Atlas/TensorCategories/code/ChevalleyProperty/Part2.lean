/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ChevalleyProperty.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.SemisimpleMultitensor
import Structure.v1.Atlas.TensorCategories.code.ChevalleyProperty
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v u


noncomputable section

namespace CategoryTheory

section LoewyLength

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

variable {C}

/-- The Loewy length `Lw(X)` of an object `X`, defined as the smallest `n` for which a
semisimple filtration of length `n` exists. -/
def LoewyLengthData.loewyLength (LD : LoewyLengthData C) (X : C) : ℕ :=
  @Nat.find _ (LD.hasSemisimpleFiltration_dec X) (LD.hasSemisimpleFiltration_exists X)

/-- In a semisimple category every object is already semisimple, so the Loewy length data
is trivially given by length `1` filtrations. -/
def loewyLengthDataOfSemisimple [IsSemisimpleCategory C] : LoewyLengthData C where
  hasSemisimpleFiltration := fun _ n => n ≥ 1
  hasSemisimpleFiltration_dec := fun _ => inferInstance
  hasSemisimpleFiltration_exists := fun _ => ⟨1, le_refl 1⟩
  hasSemisimpleFiltration_pos := fun _ _ h => h
  toFiltration := fun X n _ =>
    { gradedPiece := fun _ => X
      gradedPiece_semisimple := fun _ => IsSemisimpleCategory.semisimple X }
  filtration_tensor := fun X Y m n hm hn fX fY => by
    have hmn : m + n - 1 ≥ 1 := by omega

    set T := fX.gradedPiece ⟨0, by omega⟩ ⊗ fY.gradedPiece ⟨0, by omega⟩

    let pairs : Fin 1 → C := fun _ => T
    refine ⟨fun _ => T,
      fun r => ⟨1, pairs, inferInstance,
        fun _ => ⟨⟨0, by omega⟩, ⟨0, by omega⟩, rfl⟩,
        ⟨(biproductUniqueIso pairs).symm⟩⟩,
      fun _ => hmn⟩
  semisimple_biproduct := fun _ _ _ => IsSemisimpleCategory.semisimple _

end LoewyLength
end CategoryTheory
end
