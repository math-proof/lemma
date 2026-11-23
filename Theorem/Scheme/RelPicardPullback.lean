module

public import Mathlib
public import Def.AlgebraicGeometry_RelativePicardFunctor
public import Theorem.Scheme.RepresentsRelSubPic
public import Def.AlgebraicGeometry_RelPicardAlgEquivZeroCut
public import Structure.JacJ1Iface

public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian Scheme

noncomputable section

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
  (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)

public theorem rigSection_curveChange {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    rigSection c' t ε' ≫ curveChange f hf t = rigSection c t ε := by
  apply pullback.hom_ext
  · simp only [rigSection, curveChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hε]
  · simp only [rigSection, curveChange, Category.assoc, pullback.lift_snd, Category.comp_id]


public theorem curveChange_baseChangeSnd {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    curveChange f hf t' ≫ baseChangeSnd c ψ = baseChangeSnd c' ψ ≫ curveChange f hf t := by
  apply pullback.hom_ext <;>
    simp only [curveChange, baseChangeSnd, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]


public theorem curveChange_snd {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    curveChange f hf t ≫ pullback.snd c t = pullback.snd c' t := by
  simp only [curveChange, pullback.lift_snd, Category.comp_id]


public theorem RigidifiedLineBundle.pullbackCurve_congr {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {M M' : RigidifiedLineBundle c ε t} (h : Nonempty (M.L ≅ M'.L)) :
    Nonempty ((M.pullbackCurve f hf hε).L ≅ (M'.pullbackCurve f hf hε).L) :=
  ⟨(Scheme.Modules.pullback _).mapIso h.some⟩


public theorem FibrewiseAlgEquivZero.pullbackCurve {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {M : RigidifiedLineBundle c ε t} (hM : FibrewiseAlgEquivZero M) :
    FibrewiseAlgEquivZero (M.pullbackCurve f hf hε) := by
  intro k _ _ s

  let e : Limits.pullback (pullback.snd c' t) s ⟶ Limits.pullback (pullback.snd c t) s :=
    pullback.map _ _ _ _ (curveChange f hf t) (𝟙 _) (𝟙 T)
      (by rw [Category.comp_id, curveChange_snd]) (by simp)
  have he : e ≫ fibreAt c t s = fibreAt c' t s := by
    simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e ≫ pullback.fst (pullback.snd c t) s =
      pullback.fst (pullback.snd c' t) s ≫ curveChange f hf t := by
    simp only [e, pullback.lift_fst]
  refine IsAlgEquivZero.of_iso ?_ ((hM k s).pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm

namespace RepresentsRelSubPic

variable {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')


public theorem postComp_pullbackHom_classify {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) (hM : (algEquivZeroCut c ε).P t M) :
    postComp (pullbackHom f hf hε h h') (h.classify t M hM) =
      h'.classify t (M.pullbackCurve f hf hε) (FibrewiseAlgEquivZero.pullbackCurve f hf hε hM) := by
  refine h'.classify_unique t _ _ _ ⟨?_⟩
  exact (h'.poincare.pullbackAlongPullbackAlongIso' _ _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso (h'.classify_spec D.toBase _ _).some ≪≫
    (h.poincare.pullbackCurvePullbackAlongIso f hf hε _) ≪≫
    (Scheme.Modules.pullback _).mapIso (h.classify_spec t M hM).some


public theorem pullbackHom_unique (g : SchemeHomOver D.toBase D'.toBase)
    (hg : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
      (hM : (algEquivZeroCut c ε).P t M),
      postComp g (h.classify t M hM) =
        h'.classify t (M.pullbackCurve f hf hε) (FibrewiseAlgEquivZero.pullbackCurve f hf hε hM)) :
    g = pullbackHom f hf hε h h' := by
  have hid : h.classify D.toBase h.poincare h.poincare_mem = ⟨𝟙 _, Category.id_comp _⟩ :=
    (h.classify_unique D.toBase _ _ _ ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_id c D.toBase)).app _ ≪≫
      (Scheme.Modules.pullbackId _).app _⟩).symm
  have := hg D.toBase h.poincare h.poincare_mem
  rw [hid] at this
  refine Eq.trans ?_ this
  apply Subtype.ext
  simp [postComp]


public theorem zeroSection_pullbackHom :
    D.zeroSection ≫ (pullbackHom f hf hε h h').1 = D'.zeroSection := by
  have key := h'.ext_of_iso (𝟙 _)
    (postComp (pullbackHom f hf hε h h') ⟨D.zeroSection, D.zeroSection_toBase⟩)
    ⟨D'.zeroSection, D'.zeroSection_toBase⟩ ⟨?_⟩
  · exact congrArg Subtype.val key
  · exact (h'.poincare.pullbackAlongPullbackAlongIso' _ _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso (h'.classify_spec D.toBase _ _).some ≪≫
      (h.poincare.pullbackCurvePullbackAlongIso f hf hε _) ≪≫
      (Scheme.Modules.pullback _).mapIso h.zero.some ≪≫
      RigidifiedLineBundle.unitPullbackCurveIso f hf hε _ ≪≫ h'.zero.some.symm


public theorem existsUnique_pullbackHom :
    ∃! fstar : SchemeHomOver D.toBase D'.toBase,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
        (hM : (algEquivZeroCut c ε).P t M),
        postComp fstar (h.classify t M hM) =
          h'.classify t (M.pullbackCurve f hf hε) (FibrewiseAlgEquivZero.pullbackCurve f hf hε hM) :=
  ⟨pullbackHom f hf hε h h', fun t M hM => postComp_pullbackHom_classify f hf hε h h' t M hM,
    fun g hg => pullbackHom_unique f hf hε h h' g hg⟩

end RepresentsRelSubPic

end AlgebraicGeometry.RelPicard

end
