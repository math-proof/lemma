/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ChevalleyProperty.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.SemisimpleMultitensor
import Class.v1.Atlas.TensorCategories.code.ChevalleyProperty.Part2
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v u


noncomputable section

namespace CategoryTheory

section LoewyLength

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

/-- A length-`n` semisimple filtration of an object `X`: a tuple of `n` semisimple objects
intended as the associated graded pieces of a filtration of `X`. -/
structure SemisimpleFiltration (X : C) (n : ℕ) where
  gradedPiece : Fin n → C
  gradedPiece_semisimple : ∀ i, IsSemisimpleObject C (gradedPiece i)

/-- Abstract data witnessing the existence of a Loewy length function on `C`: every object
admits some semisimple filtration of positive length, filtrations are functorial in tensor
products with multiplicative compatible length, and biproducts of semisimple objects are
semisimple. -/
structure LoewyLengthData where
  hasSemisimpleFiltration : C → ℕ → Prop
  hasSemisimpleFiltration_dec : ∀ (X : C), DecidablePred (hasSemisimpleFiltration X)
  hasSemisimpleFiltration_exists : ∀ (X : C), ∃ n, hasSemisimpleFiltration X n
  hasSemisimpleFiltration_pos : ∀ (X : C) (n : ℕ),
    hasSemisimpleFiltration X n → 1 ≤ n
  toFiltration : ∀ (X : C) (n : ℕ),
    hasSemisimpleFiltration X n → SemisimpleFiltration C X n
  filtration_tensor :
    ∀ (X Y : C) (m n : ℕ) (_ : m ≥ 1) (_ : n ≥ 1)
    (fX : SemisimpleFiltration C X m) (fY : SemisimpleFiltration C Y n),
    ∃ (candidateGradedPieces : Fin (m + n - 1) → C),

      (∀ (r : Fin (m + n - 1)),
        ∃ (k : ℕ) (pairs : Fin k → C) (hb : HasBiproduct pairs),
          (∀ p, ∃ (i : Fin m) (j : Fin n),
            pairs p = fX.gradedPiece i ⊗ fY.gradedPiece j) ∧
          Nonempty (candidateGradedPieces r ≅ @biproduct _ _ _ _ pairs hb)) ∧

      ((∀ r, IsSemisimpleObject C (candidateGradedPieces r)) →
        hasSemisimpleFiltration (X ⊗ Y) (m + n - 1))
  semisimple_biproduct : ∀ {k : ℕ} (f : Fin k → C) (hb : HasBiproduct f),
    (∀ i, IsSemisimpleObject C (f i)) →
    IsSemisimpleObject C (@biproduct _ _ _ _ f hb)

end LoewyLength
end CategoryTheory
end
