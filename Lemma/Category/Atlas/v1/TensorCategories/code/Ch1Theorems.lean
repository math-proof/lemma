import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.Ch1Theorems
open CategoryTheory MonoidalCategory Limits


/--
[isStrictMonoidal_of_skeletal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Ch1Theorems.lean)
-/
@[path]
lemma isStrictMonoidal_of_skeletal
  [Category C]
  [MonoidalCategory C]
-- given
  (hC : Skeletal C) :
-- imply
  IsStrictMonoidal C where tensorObj_assoc X Y Z :=
-- proof
  hC ⟨α_ X Y Z⟩
    tensorUnit_left X := hC ⟨λ_ X⟩
    tensorUnit_right X := hC ⟨ρ_ X⟩

/--
[Theorem_1_15_1_endUnit_semisimple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Ch1Theorems.lean)
-/
@[path]
lemma Theorem_1_15_1_endUnit_semisimple
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [inst_ab : Abelian C]
  [TensorCategories.MonoidalBiexact C]
  [IsArtinianRing (End (𝟙_ C))] :
-- imply
  IsSemisimpleRing (End (𝟙_ C)) :=
-- proof
  TensorCategories.Theorem_1_15_1_endUnit_semisimple


-- created on 2026-10-23
