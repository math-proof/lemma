import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.TensorCategories.code.ChevalleyProperty.Part2
open CategoryTheory MonoidalCategory CategoryTheory.Limits


namespace CategoryTheory

/--
[LoewyLengthData.loewyLength_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ChevalleyProperty.lean)
-/
@[path]
lemma LoewyLengthData.loewyLength_spec
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [HasZeroMorphisms C]
  {C}
  {LD : LoewyLengthData C}
  {X : C} :
-- imply
  LD.hasSemisimpleFiltration X (LD.loewyLength X) :=
-- proof
  @Nat.find_spec _ (LD.hasSemisimpleFiltration_dec X)
    (LD.hasSemisimpleFiltration_exists X)

end CategoryTheory

namespace CategoryTheory

/--
[LoewyLengthData.loewyLength_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ChevalleyProperty.lean)
-/
@[path]
lemma LoewyLengthData.loewyLength_le
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [HasZeroMorphisms C]
  {C}
  {LD : LoewyLengthData C}
  {X : C}
  {n : ℕ}
-- given
  (h : LD.hasSemisimpleFiltration X n) :
-- imply
  LD.loewyLength X ≤ n :=
-- proof
  @Nat.find_le _ _ (LD.hasSemisimpleFiltration_dec X)
    (LD.hasSemisimpleFiltration_exists X) h

end CategoryTheory

namespace CategoryTheory

/--
[LoewyLengthData.loewyLength_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ChevalleyProperty.lean)
-/
@[path]
lemma LoewyLengthData.loewyLength_pos
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [HasZeroMorphisms C]
  {C}
  {LD : LoewyLengthData C}
  {X : C} :
-- imply
  1 ≤ LD.loewyLength X :=
-- proof
  LD.hasSemisimpleFiltration_pos X _ (LD.loewyLength_spec X)

end CategoryTheory

namespace CategoryTheory

/--
[LoewyLengthData.loewyLength_tensor_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ChevalleyProperty.lean)
-/
@[path]
lemma LoewyLengthData.loewyLength_tensor_le
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [HasZeroMorphisms C]
  {C}
  [hChev : HasChevalleyProperty C]
  {LD : LoewyLengthData C}
  {X Y : C} :
-- imply
  LD.loewyLength (X ⊗ Y) ≤ LD.loewyLength X + LD.loewyLength Y - 1 := by
-- proof
  have hX := LD.loewyLength_spec X
  have hY := LD.loewyLength_spec Y
  have hXpos := LD.loewyLength_pos X
  have hYpos := LD.loewyLength_pos Y
  let fX := LD.toFiltration X _ hX
  let fY := LD.toFiltration Y _ hY
  obtain ⟨candidateGP, hdecomp, hvalid⟩ :=
    LD.filtration_tensor X Y _ _ hXpos hYpos fX fY
  have hss : ∀ r, IsSemisimpleObject C (candidateGP r) := by
    intro r
    obtain ⟨k, pairs, hb, hpairs_are_tensors, ⟨iso_r⟩⟩ := hdecomp r
    have hpairs_ss : ∀ p, IsSemisimpleObject C (pairs p) := by
      intro p
      obtain ⟨i, j, heq⟩ := hpairs_are_tensors p
      rw [heq]
      exact hChev.tensor_semisimple _ _
        (fX.gradedPiece_semisimple i) (fY.gradedPiece_semisimple j)
    exact isSemisimpleObject_of_iso iso_r (LD.semisimple_biproduct pairs hb hpairs_ss)
  exact LD.loewyLength_le _ _ (hvalid hss)

end CategoryTheory

namespace CategoryTheory

/--
[LoewyLengthData.loewyLength_tensor_le'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ChevalleyProperty.lean)
-/
@[path]
lemma LoewyLengthData.loewyLength_tensor_le'
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [HasZeroMorphisms C]
  {C}
  [HasChevalleyProperty C]
  {LD : LoewyLengthData C}
  {X Y : C} :
-- imply
  LD.loewyLength (X ⊗ Y) + 1 ≤ LD.loewyLength X + LD.loewyLength Y := by
-- proof
  have h := LD.loewyLength_tensor_le X Y
  have hX := LD.loewyLength_pos X
  have hY := LD.loewyLength_pos Y
  omega

end CategoryTheory

namespace CategoryTheory

/--
[Proposition_1_31_3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ChevalleyProperty.lean)
-/
@[path]
lemma Proposition_1_31_3
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [HasZeroMorphisms C]
  {C}
  [HasChevalleyProperty C]
  {LD : LoewyLengthData C}
  {X Y : C} :
-- imply
  LD.loewyLength (X ⊗ Y) ≤ LD.loewyLength X + LD.loewyLength Y - 1 :=
-- proof
  LD.loewyLength_tensor_le X Y

end CategoryTheory

namespace CategoryTheory

/--
[pointed_coradicalFiltration_isHopfAlgebraFiltration](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ChevalleyProperty.lean)
-/
@[path]
lemma pointed_coradicalFiltration_isHopfAlgebraFiltration
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [HasZeroMorphisms C]
  {C}
  [hChev : HasChevalleyProperty C]
  {LD : LoewyLengthData C} :
-- imply
  IsHopfAlgebraFiltration C LD where filtration_tensor_compat := by
-- proof
  intro X Y i j hi hj
  have h := LD.loewyLength_tensor_le X Y
  have hX := LD.loewyLength_pos X
  have hY := LD.loewyLength_pos Y
  omega

end CategoryTheory


-- created on 2026-10-23
