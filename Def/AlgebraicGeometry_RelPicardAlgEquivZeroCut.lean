import Mathlib
import Def.AlgebraicGeometry_RelativePicardFunctor
import Lemma.AlgebraicGeometry.RepresentsRelSubPic

set_option autoImplicit false

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits NeronModelInfra

universe u

variable {R : Type u} [CommRing R]

noncomputable def fibreAt {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) :
    pullback (pullback.snd c t) s ⟶ Spec (CommRingCat.of k) :=
  pullback.snd _ _

def IsAlgEquivZero {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k)) (L : A.Modules) : Prop :=
  ∃ (T' : Scheme.{u}) (h : T' ⟶ Spec (CommRingCat.of k)) (_ : LocallyOfFiniteType h) (_ : GeometricallyIntegral h)
    (M : (pullback a h).Modules) (_ : Scheme.Modules.IsInvertible M)
    (t₀ t₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h),
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd a t₀)).obj M ≅
        SheafOfModules.unit (pullback a (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf) ∧
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd a t₁)).obj M ≅
        (Scheme.Modules.pullback (pullback.fst a (𝟙 (Spec (CommRingCat.of k))))).obj L)

variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

def FibrewiseAlgEquivZero {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
    IsAlgEquivZero (fibreAt c t s) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj M.L)

theorem IsAlgEquivZero.of_iso {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    {L L' : A.Modules} (e : L ≅ L') (hL : IsAlgEquivZero a L) : IsAlgEquivZero a L' := by
  obtain ⟨T', h, hft, hgi, M, hM, t₀, t₁, e₀, ⟨e₁⟩⟩ := hL
  exact ⟨T', h, hft, hgi, M, hM, t₀, t₁, e₀, ⟨e₁ ≪≫ (Scheme.Modules.pullback _).mapIso e⟩⟩

theorem IsAlgEquivZero.pullback {k : Type u} [Field k] {A A' : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    {a' : A' ⟶ Spec (CommRingCat.of k)} (e : A' ⟶ A) (he : e ≫ a = a') {L : A.Modules}
    (hL : IsAlgEquivZero a L) : IsAlgEquivZero a' ((Scheme.Modules.pullback e).obj L) := by
  obtain ⟨T', h, hft, hgi, M, hM, t₀, t₁, ⟨e₀⟩, ⟨e₁⟩⟩ := hL

  let eT : Limits.pullback a' h ⟶ Limits.pullback a h :=
    pullback.map a' h a h e (𝟙 T') (𝟙 _) (by rw [Category.comp_id, he]) (by simp)
  let e1 : Limits.pullback a' (𝟙 (Spec (CommRingCat.of k))) ⟶ Limits.pullback a (𝟙 (Spec (CommRingCat.of k))) :=
    pullback.map a' (𝟙 _) a (𝟙 _) e (𝟙 _) (𝟙 _) (by rw [Category.comp_id, he]) (by simp)
  have hsq : ∀ tt : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h,
      baseChangeSnd a' tt ≫ eT = e1 ≫ baseChangeSnd a tt := by
    intro tt
    apply pullback.hom_ext <;>
      simp only [eT, e1, baseChangeSnd, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id]
  have hfst : e1 ≫ pullback.fst a (𝟙 _) = pullback.fst a' (𝟙 _) ≫ e := by
    simp only [e1, pullback.lift_fst]
  refine ⟨T', h, hft, hgi, (Scheme.Modules.pullback eT).obj M, hM.pullback eT, t₀, t₁, ⟨?_⟩, ⟨?_⟩⟩
  · exact (Scheme.Modules.pullbackComp _ _).app M ≪≫
      (Scheme.Modules.pullbackCongr (hsq t₀)).app M ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M).symm ≪≫
      (Scheme.Modules.pullback e1).mapIso e₀ ≪≫
      Scheme.Modules.pullbackUnitIso e1
  · exact (Scheme.Modules.pullbackComp _ _).app M ≪≫
      (Scheme.Modules.pullbackCongr (hsq t₁)).app M ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M).symm ≪≫
      (Scheme.Modules.pullback e1).mapIso e₁ ≪≫
      (Scheme.Modules.pullbackComp _ _).app L ≪≫
      (Scheme.Modules.pullbackCongr hfst).app L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app L).symm

theorem geometricallyIntegral_id_Spec (k : Type u) [Field k] :
    GeometricallyIntegral (𝟙 (Spec (CommRingCat.of k))) := by
  constructor
  intro K _ y Z fst snd hP
  haveI : IsIso snd := hP.isIso_snd_of_isIso
  exact AlgebraicGeometry.IsIntegral.of_isIso (inv snd)

theorem fibrewiseAlgEquivZero_unit {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    FibrewiseAlgEquivZero (RigidifiedLineBundle.unit (c := c) (ε := ε) t) := by
  intro k _ _ s
  refine ⟨Spec (CommRingCat.of k), 𝟙 _, inferInstance, geometricallyIntegral_id_Spec k,
    SheafOfModules.unit (Limits.pullback (fibreAt c t s) (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf,
    Scheme.Modules.isInvertible_unit _, ⟨𝟙 _, Category.comp_id _⟩, ⟨𝟙 _, Category.comp_id _⟩,
    ⟨Scheme.Modules.pullbackUnitIso _⟩, ⟨?_⟩⟩
  exact Scheme.Modules.pullbackUnitIso _ ≪≫ (Scheme.Modules.pullbackUnitIso _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso (Scheme.Modules.pullbackUnitIso _).symm

theorem FibrewiseAlgEquivZero.congr {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {M M' : RigidifiedLineBundle c ε t} (h : Nonempty (M.L ≅ M'.L)) (hM : FibrewiseAlgEquivZero M) :
    FibrewiseAlgEquivZero M' := by
  intro k _ _ s
  exact (hM k s).of_iso ((Scheme.Modules.pullback _).mapIso h.some)

theorem FibrewiseAlgEquivZero.pullback {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) {M : RigidifiedLineBundle c ε t}
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (M.pullbackAlong ψ) := by
  intro k _ _ s'
  have hψ : pullback.snd c t' ≫ ψ.1 = baseChangeSnd c ψ ≫ pullback.snd c t := by
    simp only [baseChangeSnd, pullback.lift_snd]

  let e : Limits.pullback (pullback.snd c t') s' ⟶ Limits.pullback (pullback.snd c t) (s' ≫ ψ.1) :=
    pullback.map _ _ _ _ (baseChangeSnd c ψ) (𝟙 _) ψ.1 hψ (by simp)
  have he : e ≫ fibreAt c t (s' ≫ ψ.1) = fibreAt c t' s' := by
    simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e ≫ pullback.fst (pullback.snd c t) (s' ≫ ψ.1) =
      pullback.fst (pullback.snd c t') s' ≫ baseChangeSnd c ψ := by
    simp only [e, pullback.lift_fst]
  refine IsAlgEquivZero.of_iso ?_ ((hM k (s' ≫ ψ.1)).pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm

noncomputable def algEquivZeroCut (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    SubPicCondition c ε where
  P := fun _ M => FibrewiseAlgEquivZero M
  unit_mem := fun t => fibrewiseAlgEquivZero_unit t
  congr := fun _ _ _ h hM => hM.congr h
  pullback_mem := fun _ _ ψ _ hM => hM.pullback ψ

end AlgebraicGeometry.RelPicard
