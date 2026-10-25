import Mathlib
import Lemma.AlgebraicGeometry.NeronModelPropertyBundleCarrier

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronModelInfra

section ValueFunctoriality

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable {X Y Z : Scheme.{u}}

theorem genericFibreRestrict_val_eq_id (f : X ⟶ Spec (CommRingCat.of R))
    (χ : SchemeHomOver f f) (hχ : χ.1 = 𝟙 X) :
    (genericFibreRestrict R K f f χ).1 =
      𝟙 (pullback f (specGenericFibreInclusion R K)) := by
  apply pullback.hom_ext
  · simp [genericFibreRestrict, hχ]
  · simp [genericFibreRestrict, pullback.lift_snd]

theorem genericFibreRestrict_val_eq_comp (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R)) (e : Z ⟶ Spec (CommRingCat.of R))
    (φ : SchemeHomOver g f) (ψ : SchemeHomOver f e) (χ : SchemeHomOver g e)
    (hχ : χ.1 = φ.1 ≫ ψ.1) :
    (genericFibreRestrict R K e g χ).1 =
      (genericFibreRestrict R K f g φ).1 ≫ (genericFibreRestrict R K e f ψ).1 := by
  apply pullback.hom_ext
  · simp [genericFibreRestrict, hχ, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp [genericFibreRestrict, pullback.lift_snd]

end ValueFunctoriality

section MinimalModelLemma

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable {X : Scheme.{u}}

theorem neronModel_end_eq_id_of_restrict_val_eq_id (f : X ⟶ Spec (CommRingCat.of R))
    (hN : NeronUniqueExtension R K f) (hsf : Smooth f) (w : SchemeHomOver f f)
    (hw : (genericFibreRestrict R K f f w).1 =
      𝟙 (pullback f (specGenericFibreInclusion R K))) :
    w.1 = 𝟙 X := by
  have hres : genericFibreRestrict R K f f w =
      genericFibreRestrict R K f f ⟨𝟙 X, Category.id_comp f⟩ := by
    apply Subtype.ext
    rw [hw, genericFibreRestrict_val_eq_id R K f ⟨𝟙 X, Category.id_comp f⟩ rfl]
  have hwid : w = (⟨𝟙 X, Category.id_comp f⟩ : SchemeHomOver f f) :=
    (hN X f hsf).1 hres
  exact congrArg Subtype.val hwid

end MinimalModelLemma

section TwoModels

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable {X X' : Scheme.{u}}

theorem neronTwoModels_extension_unique
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf' : NeronUniqueExtension R K f') (hsf : Smooth f)
    {u₁ u₂ : SchemeHomOver f f'}
    (h : genericFibreRestrict R K f' f u₁ = genericFibreRestrict R K f' f u₂) :
    u₁ = u₂ :=
  (hNf' X f hsf).1 h

theorem neronTwoModels_existsUnique_homExtension
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf' : NeronUniqueExtension R K f') (hsf : Smooth f)
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))) :
    ∃! u : SchemeHomOver f f', genericFibreRestrict R K f' f u = uK :=
  (hNf' X f hsf).existsUnique uK

theorem neronTwoModels_comp_eq_id
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hsf : Smooth f)
    {uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))}
    {vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))}
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    {u : SchemeHomOver f f'} {v : SchemeHomOver f' f}
    (hu : genericFibreRestrict R K f' f u = uK)
    (hv : genericFibreRestrict R K f f' v = vK) :
    u.1 ≫ v.1 = 𝟙 X := by
  have hcomp : (u.1 ≫ v.1) ≫ f = f := by rw [Category.assoc, v.2, u.2]
  have hval : (genericFibreRestrict R K f f ⟨u.1 ≫ v.1, hcomp⟩).1 =
      𝟙 (pullback f (specGenericFibreInclusion R K)) := by
    rw [genericFibreRestrict_val_eq_comp R K f' f f u v ⟨u.1 ≫ v.1, hcomp⟩ rfl, hu, hv]
    exact huv
  exact neronModel_end_eq_id_of_restrict_val_eq_id R K f hNf hsf ⟨u.1 ≫ v.1, hcomp⟩ hval

theorem neronTwoModels_exists_isoExtension
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hNf' : NeronUniqueExtension R K f')
    (hsf : Smooth f) (hsf' : Smooth f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K)))
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K))) :
    ∃ (u : SchemeHomOver f f') (v : SchemeHomOver f' f),
      genericFibreRestrict R K f' f u = uK ∧
      genericFibreRestrict R K f f' v = vK ∧
      u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' := by
  obtain ⟨u, hu⟩ := (hNf' X f hsf).2 uK
  obtain ⟨v, hv⟩ := (hNf X' f' hsf').2 vK
  exact ⟨u, v, hu, hv, neronTwoModels_comp_eq_id hNf hsf huv hu hv,
    neronTwoModels_comp_eq_id hNf' hsf' hvu hv hu⟩

theorem neronTwoModels_existsUnique_isoExtension
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hNf' : NeronUniqueExtension R K f')
    (hsf : Smooth f) (hsf' : Smooth f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K)))
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K))) :
    ∃! u : SchemeHomOver f f',
      genericFibreRestrict R K f' f u = uK ∧
      ∃ v : SchemeHomOver f' f,
        genericFibreRestrict R K f f' v = vK ∧
        u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' := by
  obtain ⟨u, v, hu, hv, huvId, hvuId⟩ :=
    neronTwoModels_exists_isoExtension hNf hNf' hsf hsf' uK vK huv hvu
  refine ⟨u, ⟨hu, v, hv, huvId, hvuId⟩, ?_⟩
  rintro u₂ ⟨hu₂, -⟩
  exact neronTwoModels_extension_unique hNf' hsf (hu₂.trans hu.symm)

theorem neronTwoModels_isoExtension_isIso
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hNf' : NeronUniqueExtension R K f')
    (hsf : Smooth f) (hsf' : Smooth f')
    {uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))}
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K)))
    {u : SchemeHomOver f f'} (hu : genericFibreRestrict R K f' f u = uK) :
    IsIso u.1 := by
  obtain ⟨v, hv⟩ := (hNf X' f' hsf').2 vK
  exact ⟨⟨v.1, neronTwoModels_comp_eq_id hNf hsf huv hu hv,
    neronTwoModels_comp_eq_id hNf' hsf' hvu hv hu⟩⟩

theorem neronTwoModels_existsUnique_isoExtension_of_isIso
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (hNf : NeronUniqueExtension R K f) (hNf' : NeronUniqueExtension R K f')
    (hsf : Smooth f) (hsf' : Smooth f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))) [IsIso uK.1] :
    ∃! u : SchemeHomOver f f',
      genericFibreRestrict R K f' f u = uK ∧
      ∃ v : SchemeHomOver f' f,
        (genericFibreRestrict R K f f' v).1 = inv uK.1 ∧
        u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' := by
  have hvKmem : inv uK.1 ≫ pullback.snd f (specGenericFibreInclusion R K) =
      pullback.snd f' (specGenericFibreInclusion R K) :=
    (IsIso.inv_comp_eq uK.1).mpr uK.2.symm
  obtain ⟨u, ⟨hu, v, hv, huvId, hvuId⟩, -⟩ :=
    neronTwoModels_existsUnique_isoExtension hNf hNf' hsf hsf' uK ⟨inv uK.1, hvKmem⟩
      (IsIso.hom_inv_id uK.1) (IsIso.inv_hom_id uK.1)
  refine ⟨u, ⟨hu, v, congrArg Subtype.val hv, huvId, hvuId⟩, ?_⟩
  rintro u₂ ⟨hu₂, -⟩
  exact neronTwoModels_extension_unique hNf' hsf (hu₂.trans hu.symm)

end TwoModels

section BundleForm

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K]
variable {X X' : Scheme.{u}}
variable {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}

theorem NeronModelPropertyBundle.exists_isoExtension
    (h : NeronModelPropertyBundle R K f) (h' : NeronModelPropertyBundle R K f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K)))
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K))) :
    ∃ (u : SchemeHomOver f f') (v : SchemeHomOver f' f),
      genericFibreRestrict R K f' f u = uK ∧
      genericFibreRestrict R K f f' v = vK ∧
      u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' :=
  neronTwoModels_exists_isoExtension h.neronMapping h'.neronMapping h.smooth h'.smooth
    uK vK huv hvu

theorem NeronModelPropertyBundle.existsUnique_isoExtension
    (h : NeronModelPropertyBundle R K f) (h' : NeronModelPropertyBundle R K f')
    (uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K)))
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K))) :
    ∃! u : SchemeHomOver f f',
      genericFibreRestrict R K f' f u = uK ∧
      ∃ v : SchemeHomOver f' f,
        genericFibreRestrict R K f f' v = vK ∧
        u.1 ≫ v.1 = 𝟙 X ∧ v.1 ≫ u.1 = 𝟙 X' :=
  neronTwoModels_existsUnique_isoExtension h.neronMapping h'.neronMapping h.smooth h'.smooth
    uK vK huv hvu

theorem NeronModelPropertyBundle.isoExtension_isIso
    (h : NeronModelPropertyBundle R K f) (h' : NeronModelPropertyBundle R K f')
    {uK : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f' (specGenericFibreInclusion R K))}
    (vK : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (huv : uK.1 ≫ vK.1 = 𝟙 (pullback f (specGenericFibreInclusion R K)))
    (hvu : vK.1 ≫ uK.1 = 𝟙 (pullback f' (specGenericFibreInclusion R K)))
    {u : SchemeHomOver f f'} (hu : genericFibreRestrict R K f' f u = uK) :
    IsIso u.1 :=
  neronTwoModels_isoExtension_isIso h.neronMapping h'.neronMapping h.smooth h'.smooth
    vK huv hvu hu

end BundleForm

section SatGates

theorem gate_neronModel_end_eq_id_trivialGroupScheme_zp (p : ℕ) [Fact p.Prime]
    (w : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ_[p]))) (𝟙 (Spec (CommRingCat.of ℤ_[p]))))
    (hw : (genericFibreRestrict ℤ_[p] ℚ_[p] (𝟙 (Spec (CommRingCat.of ℤ_[p])))
        (𝟙 (Spec (CommRingCat.of ℤ_[p]))) w).1 =
      𝟙 (pullback (𝟙 (Spec (CommRingCat.of ℤ_[p])))
        (specGenericFibreInclusion ℤ_[p] ℚ_[p]))) :
    w.1 = 𝟙 (Spec (CommRingCat.of ℤ_[p])) :=
  neronModel_end_eq_id_of_restrict_val_eq_id ℤ_[p] ℚ_[p] (𝟙 (Spec (CommRingCat.of ℤ_[p])))
    (gate_neronModelPropertyBundle_trivialGroupScheme_zp p).neronMapping
    (gate_neronModelPropertyBundle_trivialGroupScheme_zp p).smooth w hw

theorem gate_neronTwoModels_exists_isoExtension_trivialGroupScheme_zp (p : ℕ) [Fact p.Prime] :
    ∃ (u v : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ_[p])))
        (𝟙 (Spec (CommRingCat.of ℤ_[p])))),
      genericFibreRestrict ℤ_[p] ℚ_[p] (𝟙 (Spec (CommRingCat.of ℤ_[p])))
          (𝟙 (Spec (CommRingCat.of ℤ_[p]))) u =
        ⟨𝟙 (pullback (𝟙 (Spec (CommRingCat.of ℤ_[p])))
            (specGenericFibreInclusion ℤ_[p] ℚ_[p])), Category.id_comp _⟩ ∧
      genericFibreRestrict ℤ_[p] ℚ_[p] (𝟙 (Spec (CommRingCat.of ℤ_[p])))
          (𝟙 (Spec (CommRingCat.of ℤ_[p]))) v =
        ⟨𝟙 (pullback (𝟙 (Spec (CommRingCat.of ℤ_[p])))
            (specGenericFibreInclusion ℤ_[p] ℚ_[p])), Category.id_comp _⟩ ∧
      u.1 ≫ v.1 = 𝟙 (Spec (CommRingCat.of ℤ_[p])) ∧
      v.1 ≫ u.1 = 𝟙 (Spec (CommRingCat.of ℤ_[p])) :=
  neronTwoModels_exists_isoExtension
    (gate_neronModelPropertyBundle_trivialGroupScheme_zp p).neronMapping
    (gate_neronModelPropertyBundle_trivialGroupScheme_zp p).neronMapping
    (gate_neronModelPropertyBundle_trivialGroupScheme_zp p).smooth
    (gate_neronModelPropertyBundle_trivialGroupScheme_zp p).smooth
    ⟨𝟙 (pullback (𝟙 (Spec (CommRingCat.of ℤ_[p])))
        (specGenericFibreInclusion ℤ_[p] ℚ_[p])), Category.id_comp _⟩
    ⟨𝟙 (pullback (𝟙 (Spec (CommRingCat.of ℤ_[p])))
        (specGenericFibreInclusion ℤ_[p] ℚ_[p])), Category.id_comp _⟩
    (Category.id_comp _) (Category.id_comp _)

theorem gate_neronTwoModels_existsUnique_isoExtension_trivialGroupScheme_z3 :
    ∃! u : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ_[3]))) (𝟙 (Spec (CommRingCat.of ℤ_[3]))),
      genericFibreRestrict ℤ_[3] ℚ_[3] (𝟙 (Spec (CommRingCat.of ℤ_[3])))
          (𝟙 (Spec (CommRingCat.of ℤ_[3]))) u =
        ⟨𝟙 (pullback (𝟙 (Spec (CommRingCat.of ℤ_[3])))
            (specGenericFibreInclusion ℤ_[3] ℚ_[3])), Category.id_comp _⟩ ∧
      ∃ v : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ_[3]))) (𝟙 (Spec (CommRingCat.of ℤ_[3]))),
        genericFibreRestrict ℤ_[3] ℚ_[3] (𝟙 (Spec (CommRingCat.of ℤ_[3])))
            (𝟙 (Spec (CommRingCat.of ℤ_[3]))) v =
          ⟨𝟙 (pullback (𝟙 (Spec (CommRingCat.of ℤ_[3])))
              (specGenericFibreInclusion ℤ_[3] ℚ_[3])), Category.id_comp _⟩ ∧
        u.1 ≫ v.1 = 𝟙 (Spec (CommRingCat.of ℤ_[3])) ∧
        v.1 ≫ u.1 = 𝟙 (Spec (CommRingCat.of ℤ_[3])) :=
  neronTwoModels_existsUnique_isoExtension
    (gate_neronModelPropertyBundle_trivialGroupScheme_z3).neronMapping
    (gate_neronModelPropertyBundle_trivialGroupScheme_z3).neronMapping
    (gate_neronModelPropertyBundle_trivialGroupScheme_z3).smooth
    (gate_neronModelPropertyBundle_trivialGroupScheme_z3).smooth
    ⟨𝟙 (pullback (𝟙 (Spec (CommRingCat.of ℤ_[3])))
        (specGenericFibreInclusion ℤ_[3] ℚ_[3])), Category.id_comp _⟩
    ⟨𝟙 (pullback (𝟙 (Spec (CommRingCat.of ℤ_[3])))
        (specGenericFibreInclusion ℤ_[3] ℚ_[3])), Category.id_comp _⟩
    (Category.id_comp _) (Category.id_comp _)

end SatGates

end NeronModelInfra

/--
info: 'NeronModelInfra.genericFibreRestrict_val_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.genericFibreRestrict_val_eq_id

/--
info: 'NeronModelInfra.genericFibreRestrict_val_eq_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.genericFibreRestrict_val_eq_comp

/--
info: 'NeronModelInfra.neronModel_end_eq_id_of_restrict_val_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronModel_end_eq_id_of_restrict_val_eq_id

/--
info: 'NeronModelInfra.neronTwoModels_extension_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronTwoModels_extension_unique

/--
info: 'NeronModelInfra.neronTwoModels_existsUnique_homExtension' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronTwoModels_existsUnique_homExtension

/--
info: 'NeronModelInfra.neronTwoModels_comp_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronTwoModels_comp_eq_id

/--
info: 'NeronModelInfra.neronTwoModels_exists_isoExtension' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronTwoModels_exists_isoExtension

/--
info: 'NeronModelInfra.neronTwoModels_existsUnique_isoExtension' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronTwoModels_existsUnique_isoExtension

/--
info: 'NeronModelInfra.neronTwoModels_isoExtension_isIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronTwoModels_isoExtension_isIso

/--
info: 'NeronModelInfra.neronTwoModels_existsUnique_isoExtension_of_isIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronTwoModels_existsUnique_isoExtension_of_isIso

/--
info: 'NeronModelInfra.NeronModelPropertyBundle.exists_isoExtension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.NeronModelPropertyBundle.exists_isoExtension

/--
info: 'NeronModelInfra.NeronModelPropertyBundle.existsUnique_isoExtension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.NeronModelPropertyBundle.existsUnique_isoExtension

/--
info: 'NeronModelInfra.NeronModelPropertyBundle.isoExtension_isIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.NeronModelPropertyBundle.isoExtension_isIso

/--
info: 'NeronModelInfra.gate_neronModel_end_eq_id_trivialGroupScheme_zp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_neronModel_end_eq_id_trivialGroupScheme_zp

/--
info: 'NeronModelInfra.gate_neronTwoModels_exists_isoExtension_trivialGroupScheme_zp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_neronTwoModels_exists_isoExtension_trivialGroupScheme_zp

/--
info: 'NeronModelInfra.gate_neronTwoModels_existsUnique_isoExtension_trivialGroupScheme_z3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_neronTwoModels_existsUnique_isoExtension_trivialGroupScheme_z3
