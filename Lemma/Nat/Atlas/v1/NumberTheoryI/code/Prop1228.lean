import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.Prop1228
open Module Ideal


attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra


/--
[different_tower](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop1228.lean)
-/
@[path]
lemma different_tower
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsDedekindDomain B]
  [Algebra A B] [Module.Finite A B] [IsTorsionFree A B]
  [CommRing C] [IsDomain C] [IsDedekindDomain C]
  [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  [Module.Finite A C] [Module.Finite B C]
  [IsTorsionFree A C] [IsTorsionFree B C]
  [Algebra.IsSeparable (FractionRing A) (FractionRing C)] :
-- imply
  differentIdeal A C = differentIdeal B C * (differentIdeal A B).map (algebraMap B C) :=
-- proof
  differentIdeal_eq_differentIdeal_mul_differentIdeal A (FractionRing A) B (FractionRing B) C

/--
[discr_tower](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop1228.lean)
-/
@[path]
lemma discr_tower
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsDedekindDomain B]
  [Algebra A B] [Module.Finite A B] [IsTorsionFree A B]
  [CommRing C] [IsDomain C] [IsDedekindDomain C]
  [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  [Module.Finite A C] [Module.Finite B C]
  [IsTorsionFree A C] [IsTorsionFree B C]
  [Algebra.IsSeparable (FractionRing A) (FractionRing C)] :
-- imply
  discrIdeal A C = (discrIdeal A B) ^ (finrank (FractionRing B) (FractionRing C)) * Ideal.spanNorm A (discrIdeal B C) := by
-- proof
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      (FractionRing A) (FractionRing B) (FractionRing C)
  have : Algebra.IsSeparable (FractionRing B) (FractionRing C) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      (FractionRing A) (FractionRing B) (FractionRing C)
  unfold discrIdeal
  rw [spanNorm_eq A (differentIdeal A C)]
  have h := different_tower (A := A) (B := B) (C := C)
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
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsDedekindDomain B]
  [Algebra A B] [Module.Finite A B] [IsTorsionFree A B]
  [CommRing C] [IsDomain C] [IsDedekindDomain C]
  [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  [Module.Finite A C] [Module.Finite B C]
  [IsTorsionFree A C] [IsTorsionFree B C]
  [Algebra.IsSeparable (FractionRing A) (FractionRing C)] :
-- imply
  (differentIdeal A C = differentIdeal B C * (differentIdeal A B).map (algebraMap B C)) ∧ (discrIdeal A C = (discrIdeal A B) ^ (finrank (FractionRing B) (FractionRing C)) * Ideal.spanNorm A (discrIdeal B C)) :=
-- proof
  ⟨different_tower (A := A) (B := B) (C := C), discr_tower (A := A) (B := B) (C := C)⟩


-- created on 2026-10-23
-- updated on 2026-10-29
