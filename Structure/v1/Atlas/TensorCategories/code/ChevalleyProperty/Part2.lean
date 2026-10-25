/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ChevalleyProperty.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.SemisimpleMultitensor
import Def.v1.Atlas.TensorCategories.code.ChevalleyProperty.Part2
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v u


noncomputable section

namespace CategoryTheory

section LoewyLength

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

variable {C}

/-- Tensor-product compatibility for a coradical-style Loewy length: the filtration is a
"Hopf algebra filtration" in the sense of Corollary 1.31.5 if `loewyLength (X ⊗ Y)` is
controlled by the sum of the Loewy lengths of `X` and `Y`. -/
structure IsHopfAlgebraFiltration (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasZeroMorphisms C] [HasChevalleyProperty C]
    (LD : LoewyLengthData C) : Prop where
  filtration_tensor_compat :
    ∀ (X Y : C) (i j : ℕ),
      LD.loewyLength X ≤ i → LD.loewyLength Y ≤ j →
      LD.loewyLength (X ⊗ Y) ≤ i + j

/-- A Hopf algebra filtration is "full" if it is also preserved by taking right duals,
matching `S(H_i) = H_i` in Corollary 1.31.5. -/
structure IsFullHopfAlgebraFiltration (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasZeroMorphisms C] [HasChevalleyProperty C]
    (LD : LoewyLengthData C) : Prop extends IsHopfAlgebraFiltration C LD where
  dual_preserves_filtration :
    ∀ (X : C) [HasRightDual X] (n : ℕ),
      LD.loewyLength X ≤ n ↔ LD.loewyLength (HasRightDual.rightDual (X := X)) ≤ n

end LoewyLength
end CategoryTheory
end
