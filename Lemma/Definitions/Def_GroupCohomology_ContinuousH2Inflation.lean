import Mathlib
import Lemma.Definitions.Def_GroupCohomology_ContinuousH2
import Lemma.Definitions.Def_GroupCohomology_LevelSubgroup

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
  (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (M : Rep k G)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F]

def levelInflate₁ :
    ((G ⧸ F.fixingSubgroup.comap r) → M.quotientToInvariants (F.fixingSubgroup.comap r)) →ₗ[k] (G → M) where
  toFun y g := (y (g : G ⧸ F.fixingSubgroup.comap r) : M)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def levelInflate₂ :
    ((G ⧸ F.fixingSubgroup.comap r) × (G ⧸ F.fixingSubgroup.comap r) →
        M.quotientToInvariants (F.fixingSubgroup.comap r)) →ₗ[k] (G × G → M) where
  toFun x p := (x ((p.1 : G ⧸ F.fixingSubgroup.comap r), (p.2 : G ⧸ F.fixingSubgroup.comap r)) : M)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma levelInflate₁_apply (y : (G ⧸ F.fixingSubgroup.comap r) → M.quotientToInvariants _) (g : G) :
    levelInflate₁ r M F y g = (y (g : G ⧸ F.fixingSubgroup.comap r) : M) := rfl

@[simp] lemma levelInflate₂_apply
    (x : (G ⧸ F.fixingSubgroup.comap r) × (G ⧸ F.fixingSubgroup.comap r) → M.quotientToInvariants _) (g h : G) :
    levelInflate₂ r M F x (g, h) = (x ((g : G ⧸ F.fixingSubgroup.comap r), (h : G ⧸ F.fixingSubgroup.comap r)) : M) :=
  rfl

section lemmas

variable {r M F}

omit [Normal ℚ F] in
private lemma coe_mul_eq_of_mem {g s : G} (hs : r s ∈ F.fixingSubgroup) :
    ((g * s : G) : G ⧸ F.fixingSubgroup.comap r) = (g : G ⧸ F.fixingSubgroup.comap r) := by
  rw [QuotientGroup.eq]; simpa using (F.fixingSubgroup.comap r).inv_mem hs

private lemma qti_coe (g : G) (v : M.quotientToInvariants (F.fixingSubgroup.comap r)) :
    (((M.quotientToInvariants (F.fixingSubgroup.comap r)).ρ (g : G ⧸ F.fixingSubgroup.comap r) v :
      M.quotientToInvariants _) : M) = M.ρ g (v : M) :=
  rfl

private lemma qti_coe' (g : G) (v : M.quotientToInvariants (F.fixingSubgroup.comap r)) :
    (((M.ρ.quotientToInvariants (F.fixingSubgroup.comap r)) (g : G ⧸ F.fixingSubgroup.comap r) v :
      M.quotientToInvariants _) : M) = M.ρ g (v : M) :=
  rfl

variable [FiniteDimensional ℚ F]

lemma levelInflate₁_mem_levelCochains₁ (y : (G ⧸ F.fixingSubgroup.comap r) → M.quotientToInvariants _) :
    levelInflate₁ r M F y ∈ levelCochains₁ r M :=
  ⟨F, inferInstance, fun g s hs => by simp only [levelInflate₁_apply, coe_mul_eq_of_mem hs]⟩

lemma levelInflate₂_mem_levelCochains₂
    (x : (G ⧸ F.fixingSubgroup.comap r) × (G ⧸ F.fixingSubgroup.comap r) → M.quotientToInvariants _) :
    levelInflate₂ r M F x ∈ levelCochains₂ r M :=
  ⟨F, inferInstance, fun g g' s s' hs hs' => by
    simp only [levelInflate₂_apply, coe_mul_eq_of_mem hs, coe_mul_eq_of_mem hs']⟩

omit [FiniteDimensional ℚ F] in
lemma levelInflate₂_d₁₂ (y : (G ⧸ F.fixingSubgroup.comap r) → M.quotientToInvariants _) :
    levelInflate₂ r M F ((d₁₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))).hom y)
      = (d₁₂ M).hom (levelInflate₁ r M F y) := by
  funext ⟨g, h⟩
  rw [levelInflate₂_apply, d₁₂_hom_apply, d₁₂_hom_apply]
  simp only [levelInflate₁_apply, QuotientGroup.mk_mul, Submodule.coe_add, Submodule.coe_sub, qti_coe']

omit [FiniteDimensional ℚ F] in
lemma levelInflate₂_mem_cocycles₂
    {x : (G ⧸ F.fixingSubgroup.comap r) × (G ⧸ F.fixingSubgroup.comap r) → M.quotientToInvariants _}
    (hx : x ∈ cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    levelInflate₂ r M F x ∈ cocycles₂ M := by
  rw [mem_cocycles₂_iff] at hx ⊢
  intro g h j
  have := congrArg Subtype.val (hx (g : G ⧸ _) (h : G ⧸ _) (j : G ⧸ _))
  simpa only [levelInflate₂_apply, Submodule.coe_add, qti_coe, qti_coe', QuotientGroup.mk_mul] using this

lemma levelInflate₂_mem_levelCocycles₂
    {x : (G ⧸ F.fixingSubgroup.comap r) × (G ⧸ F.fixingSubgroup.comap r) → M.quotientToInvariants _}
    (hx : x ∈ cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    levelInflate₂ r M F x ∈ levelCocycles₂ r M :=
  ⟨levelInflate₂_mem_cocycles₂ hx, levelInflate₂_mem_levelCochains₂ x⟩

lemma levelInflate₂_mem_levelCoboundaries₂
    {x : (G ⧸ F.fixingSubgroup.comap r) × (G ⧸ F.fixingSubgroup.comap r) → M.quotientToInvariants _}
    (hx : x ∈ coboundaries₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    levelInflate₂ r M F x ∈ levelCoboundaries₂ r M := by
  obtain ⟨y, rfl⟩ := hx
  exact (mem_levelCoboundaries₂_iff r M _).2
    ⟨levelInflate₁ r M F y, levelInflate₁_mem_levelCochains₁ y, (levelInflate₂_d₁₂ y).symm⟩

end lemmas

variable [FiniteDimensional ℚ F]

def levelInflateCocycles₂ :
    cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r)) →ₗ[k] levelCocycles₂ r M :=
  ((levelInflate₂ r M F).comp (Submodule.subtype _)).codRestrict _ fun x =>
    levelInflate₂_mem_levelCocycles₂ x.2

@[simp] lemma coe_levelInflateCocycles₂ (x : cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    (levelInflateCocycles₂ r M F x : G × G → M) = levelInflate₂ r M F x := rfl

lemma continuousH2π_levelInflateCocycles₂_eq_zero
    {x : cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))}
    (hx : (x : _ → _) ∈ coboundaries₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    continuousH2π r M (levelInflateCocycles₂ r M F x) = 0 :=
  (continuousH2π_eq_zero_iff r M _).2 (levelInflate₂_mem_levelCoboundaries₂ hx)

def continuousH2Inflation :
    H2 (M.quotientToInvariants (F.fixingSubgroup.comap r)) →ₗ[k] continuousH2 r M :=
  (Submodule.liftQ _ (continuousH2π r M ∘ₗ levelInflateCocycles₂ r M F) (by
      rintro x ⟨y, rfl⟩
      exact continuousH2π_levelInflateCocycles₂_eq_zero r M F ⟨y, rfl⟩))
    ∘ₗ (H2Iso (M.quotientToInvariants (F.fixingSubgroup.comap r))).hom.hom

@[simp] lemma continuousH2Inflation_H2π (x : cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    continuousH2Inflation r M F (H2π _ x) = continuousH2π r M (levelInflateCocycles₂ r M F x) := by
  have h := π_comp_H2Iso_hom_apply (M.quotientToInvariants (F.fixingSubgroup.comap r))
    ((isoCocycles₂ _).inv x)
  simp only [Iso.inv_hom_id_apply] at h
  have e : (H2Iso (M.quotientToInvariants (F.fixingSubgroup.comap r))).hom.hom (H2π _ x)
      = (LinearMap.range
          (shortComplexH2 (M.quotientToInvariants (F.fixingSubgroup.comap r))).moduleCatToCycles).mkQ x :=
    Eq.trans rfl h
  have key : ∀ z, z = (LinearMap.range
          (shortComplexH2 (M.quotientToInvariants (F.fixingSubgroup.comap r))).moduleCatToCycles).mkQ x →
      (LinearMap.range (shortComplexH2 (M.quotientToInvariants (F.fixingSubgroup.comap r))).moduleCatToCycles).liftQ
          (continuousH2π r M ∘ₗ levelInflateCocycles₂ r M F)
          (by rintro x ⟨y, rfl⟩; exact continuousH2π_levelInflateCocycles₂_eq_zero r M F ⟨y, rfl⟩) z
        = continuousH2π r M (levelInflateCocycles₂ r M F x) := by
    rintro _ rfl; rfl
  exact key _ e

end groupCohomology

end
