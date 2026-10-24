import Mathlib
import Lemma.Definitions.Def_GroupCohomology_LevelSubgroup
import Lemma.Definitions.Def_FieldTheory_RatAlgClosureGalois

set_option autoImplicit false

noncomputable section

namespace groupCohomology

scoped instance isAlgClosure_rat_algebraicClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩

variable {G : Type*} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

abbrev levelRestrict (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] : G →* (F ≃ₐ[ℚ] F) :=
  (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).comp r

lemma levelRestrict_apply_apply (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] (g : G) (x : F) :
    (levelRestrict r F g x : AlgebraicClosure ℚ) = r g x :=
  AlgEquiv.restrictNormal_commutes (r g) F x

lemma ker_levelRestrict (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    (levelRestrict r F).ker = F.fixingSubgroup.comap r :=
  (comap_fixingSubgroup_eq_ker r F).symm

def levelQuotientHom (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    G ⧸ F.fixingSubgroup.comap r →* (F ≃ₐ[ℚ] F) :=
  QuotientGroup.lift _ (levelRestrict r F) (by rw [← ker_levelRestrict])

@[simp] lemma levelQuotientHom_mk (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] (g : G) :
    levelQuotientHom r F (QuotientGroup.mk g) = levelRestrict r F g := rfl

lemma levelQuotientHom_injective (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    Function.Injective (levelQuotientHom r F) := by
  rw [← MonoidHom.ker_eq_bot_iff, levelQuotientHom, QuotientGroup.ker_lift, ker_levelRestrict, QuotientGroup.map_mk'_self]

def levelQuotientEquiv (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ F.fixingSubgroup.comap (MonoidHom.id _) ≃* (F ≃ₐ[ℚ] F) :=
  MulEquiv.ofBijective (levelQuotientHom (MonoidHom.id _) F)
    ⟨levelQuotientHom_injective (MonoidHom.id _) F, fun σ => by
      obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := F) (AlgebraicClosure ℚ) σ
      exact ⟨QuotientGroup.mk g, rfl⟩⟩

@[simp] lemma levelQuotientEquiv_mk (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F]
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    levelQuotientEquiv F (QuotientGroup.mk g) = AlgEquiv.restrictNormalHom F g := rfl

lemma levelQuotientEquiv_apply_apply (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F]
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : F) :
    (levelQuotientEquiv F (QuotientGroup.mk g) x : AlgebraicClosure ℚ) = g x :=
  AlgEquiv.restrictNormal_commutes g F x

end groupCohomology

namespace Rep

open scoped groupCohomology

abbrev ofLevel {k : Type} [CommRing k] (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] (A : Rep k (F ≃ₐ[ℚ] F)) :
    Rep k ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ F.fixingSubgroup.comap (MonoidHom.id _)) :=
  Rep.res (groupCohomology.levelQuotientEquiv F).toMonoidHom A

end Rep

end
