import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Prop22PicCaCl
open FractionalIdeal nonZeroDivisors


/--
[Prop22.cartier_to_pic_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop22PicCaCl.lean)
-/
@[path]
lemma Prop22.cartier_to_pic_surjective
  {R : Type*}
  [CommRing R]
  [IsDomain R] :
-- imply
  Function.Surjective (Prop22.cartierToPicHom R) := by
-- proof
  apply Function.Surjective.comp (ClassGroup.equivPic R).surjective
  intro y
  induction y using Quotient.inductionOn' with
  | h a => exact ⟨a, by rw [← ClassGroup.Quot_mk_eq_mk]; rfl⟩

/--
[Prop22.ker_cartier_to_pic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop22PicCaCl.lean)
-/
@[path]
lemma Prop22.ker_cartier_to_pic
  {R : Type*}
  [CommRing R]
  [IsDomain R] :
-- imply
  (Prop22.cartierToPicHom R).ker = (Prop22.principalHom R).range := by
-- proof
  ext x
  simp only [MonoidHom.mem_ker, Prop22.cartierToPicHom, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, map_eq_one_iff _ (ClassGroup.equivPic R).injective,
    MonoidHom.mem_range]
  constructor
  · intro h
    have : (QuotientGroup.mk x : ClassGroup R) = 1 := by
      rwa [show (QuotientGroup.mk x : ClassGroup R) =
        ClassGroup.mk (K := FractionRing R) x from by
        rw [← ClassGroup.Quot_mk_eq_mk]; rfl]
    rwa [QuotientGroup.eq_one_iff] at this
  · intro h
    have : (QuotientGroup.mk x : ClassGroup R) = 1 := by
      rwa [QuotientGroup.eq_one_iff]
    rwa [show (QuotientGroup.mk x : ClassGroup R) =
      ClassGroup.mk (K := FractionRing R) x from by
      rw [← ClassGroup.Quot_mk_eq_mk]; rfl] at this

/--
[prop22_picard_iso_classGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop22PicCaCl.lean)
-/
@[path]
lemma prop22_picard_iso_classGroup
  {R : Type*}
  [CommRing R]
  [IsDomain R] :
-- imply
  Nonempty (ClassGroup R ≃* CommRing.Pic R) :=
-- proof
  ⟨ClassGroup.equivPic R⟩

/--
[prop22_picard_iso_cartier_quotient_geometric](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop22PicCaCl.lean)
-/
@[path]
lemma prop22_picard_iso_cartier_quotient_geometric
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R] :
-- imply
  Nonempty (ClassGroup R ≃* CommRing.Pic R) :=
-- proof
  ⟨ClassGroup.equivPic R⟩


-- created on 2026-10-23
