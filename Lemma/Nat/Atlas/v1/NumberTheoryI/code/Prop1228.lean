import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Prop1228
open Module Ideal


/--
[different_tower](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop1228.lean)
-/
@[path]
lemma different_tower
  {A : Type*}
  {B : Type*}
  {C : Type*} :
-- imply
  differentIdeal A C = differentIdeal B C * (differentIdeal A B).map (algebraMap B C) :=
-- proof
  differentIdeal_eq_differentIdeal_mul_differentIdeal A B C

/--
[discr_tower](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop1228.lean)
-/
@[path]
lemma discr_tower
  {A : Type*}
  {B : Type*}
  {C : Type*} :
-- imply
  discrIdeal A C = (discrIdeal A B) ^ (finrank (FractionRing B) (FractionRing C)) * Ideal.spanNorm A (discrIdeal B C) := by
-- proof
  haveI : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      (FractionRing A) (FractionRing B) (FractionRing C)
  haveI : Algebra.IsSeparable (FractionRing B) (FractionRing C) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      (FractionRing A) (FractionRing B) (FractionRing C)
  unfold discrIdeal
  rw [spanNorm_eq A (differentIdeal A C)]
  have h := different_tower A B C
  conv_lhs => rw [h]
  rw [map_mul, mul_comm]
  congr 1
  ·
    rw [← relNorm_relNorm A B (Ideal.map (algebraMap B C) (differentIdeal A B))]
    rw [relNorm_algebraMap C (differentIdeal A B)]
    rw [map_pow]
    rw [← spanNorm_eq A (differentIdeal A B)]
  ·
    rw [← relNorm_relNorm A B (differentIdeal B C)]
    rw [← spanNorm_eq B (differentIdeal B C)]
    rw [← spanNorm_eq A (spanNorm B (differentIdeal B C))]

/--
[proposition_12_28](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop1228.lean)
-/
@[path]
lemma proposition_12_28
  {A : Type*}
  {B : Type*}
  {C : Type*} :
-- imply
  (differentIdeal A C = differentIdeal B C * (differentIdeal A B).map (algebraMap B C)) ∧ (discrIdeal A C = (discrIdeal A B) ^ (finrank (FractionRing B) (FractionRing C)) * Ideal.spanNorm A (discrIdeal B C)) :=
-- proof
  ⟨different_tower A B C, discr_tower A B C⟩


-- created on 2026-10-23
