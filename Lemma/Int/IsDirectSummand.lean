import Mathlib
import sympy.Basic
import Def.v1.Atlas.LieGroups.code.ProjectiveFunctors.Part7
open ProjectiveFunctors
open scoped TensorProduct


namespace ProjectiveFunctors

/--
[isDirectSummand_refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma isDirectSummand_refl
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {F : EndoFunctorData R 𝔤} :
-- imply
  IsDirectSummand F F :=
-- proof
  ⟨NatTransData.id F, NatTransData.id F,
    fun M x => by simp [NatTransData.comp, NatTransData.id, RepGfHom.comp, RepGfHom.id]⟩

end ProjectiveFunctors

namespace ProjectiveFunctors

/--
[tensor_functor_is_projective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma tensor_functor_is_projective
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {FV : TensorFunctorData R 𝔤} :
-- imply
  IsProjectiveFunctor FV.functor where exists_tensor_summand :=
-- proof
  ⟨FV, isDirectSummand_refl FV.functor⟩

end ProjectiveFunctors

namespace ProjectiveFunctors

/--
[evalAtVerma_bijective_of_summand](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma evalAtVerma_bijective_of_summand
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {lam : Δ.𝔥 →ₗ[R] R}
  {F₁ F₂ : ThetaFunctorData R 𝔤 Δ wg lam}
  {G₁ G₂ : ThetaFunctorData R 𝔤 Δ wg lam}
  {Mverma : RepGfObj R 𝔤}
-- given
  (hSum₁ : IsDirectSummandTheta F₁ G₁)
  (hSum₂ : IsDirectSummandTheta F₂ G₂)
  (hBij : Function.Bijective (evalAtVerma G₁ G₂ Mverma)) :
-- imply
  Function.Bijective (evalAtVerma F₁ F₂ Mverma) := by
-- proof
  obtain ⟨i₁, p₁, hp₁⟩ := hSum₁
  obtain ⟨i₂, p₂, hp₂⟩ := hSum₂
  have repGfHom_ext : ∀ {M' N' : RepGfObj R 𝔤} (f g : RepGfHom M' N'),
    (∀ x, f.toFun x = g.toFun x) → f = g := by
    intro M' N' ⟨f⟩ ⟨g⟩ h; congr; exact LieModuleHom.ext h
  have natTransData_ext : ∀ {F' G' : EndoFunctorData R 𝔤}
    (α β : NatTransData F' G'),
    (∀ (M : RepGfObj R 𝔤) (x : (F'.obj M).carrier),
      (α.app M).toFun x = (β.app M).toFun x) → α = β := by
    intro F' G' α β h
    cases α; cases β; congr; funext M
    exact repGfHom_ext _ _ (h M)
  have retract₁ : ∀ (M : RepGfObj R 𝔤) (y : (F₁.baseFunctor.obj M).carrier),
    (p₁.app M).toFun ((i₁.app M).toFun y) = y := by
    intro M y
    have h := hp₁ M y
    simp only [NatTransData.EqPointwise, RepGfHom.EqAsMap] at hp₁
    have := hp₁ M y
    simp [NatTransData.comp, RepGfHom.comp, NatTransData.id, RepGfHom.id] at this
    exact this
  have retract₂ : ∀ (M : RepGfObj R 𝔤) (z : (F₂.baseFunctor.obj M).carrier),
    (p₂.app M).toFun ((i₂.app M).toFun z) = z := by
    intro M z
    simp only [NatTransData.EqPointwise, RepGfHom.EqAsMap] at hp₂
    have := hp₂ M z
    simp [NatTransData.comp, RepGfHom.comp, NatTransData.id, RepGfHom.id] at this
    exact this
  constructor
  ·
    intro η η' heq
    have heval : (i₂.comp (η.comp p₁)).app Mverma = (i₂.comp (η'.comp p₁)).app Mverma := by
      apply repGfHom_ext
      intro x
      show (i₂.app Mverma).toFun ((η.app Mverma).toFun ((p₁.app Mverma).toFun x)) =
        (i₂.app Mverma).toFun ((η'.app Mverma).toFun ((p₁.app Mverma).toFun x))
      rw [show (η.app Mverma) = (η'.app Mverma) from heq]
    have hξeq := hBij.1 heval
    apply natTransData_ext
    intro M x
    have eq₁ : (η.app M).toFun x =
      (p₂.app M).toFun ((i₂.app M).toFun ((η.app M).toFun ((p₁.app M).toFun ((i₁.app M).toFun x)))) := by
      rw [retract₁ M x, retract₂ M]
    have eq₂ : (η'.app M).toFun x =
      (p₂.app M).toFun ((i₂.app M).toFun ((η'.app M).toFun ((p₁.app M).toFun ((i₁.app M).toFun x)))) := by
      rw [retract₁ M x, retract₂ M]
    rw [eq₁, eq₂]
    congr 1
    have hAppEq : (i₂.comp (η.comp p₁)).app M = (i₂.comp (η'.comp p₁)).app M := by rw [hξeq]
    have : ((i₂.comp (η.comp p₁)).app M).toFun ((i₁.app M).toFun x) =
      ((i₂.comp (η'.comp p₁)).app M).toFun ((i₁.app M).toFun x) := by
      rw [hAppEq]
    exact this
  ·
    intro f
    let g : RepGfHom (G₁.baseFunctor.obj Mverma) (G₂.baseFunctor.obj Mverma) :=
      (i₂.app Mverma).comp (f.comp (p₁.app Mverma))
    obtain ⟨Φ, hΦ⟩ := hBij.2 g
    use p₂.comp (Φ.comp i₁)
    apply repGfHom_ext
    intro x
    show (p₂.app Mverma).toFun ((Φ.app Mverma).toFun ((i₁.app Mverma).toFun x)) = f.toFun x
    have hΦM : Φ.app Mverma = g := hΦ
    rw [show (Φ.app Mverma).toFun = g.toFun from congrArg RepGfHom.toFun hΦM]
    show (p₂.app Mverma).toFun
      ((i₂.app Mverma).toFun (f.toFun ((p₁.app Mverma).toFun ((i₁.app Mverma).toFun x)))) = f.toFun x
    rw [retract₁ Mverma x, retract₂ Mverma]

end ProjectiveFunctors

namespace ProjectiveFunctors

/--
[exact_functor_preserves_surjection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma exact_functor_preserves_surjection
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {F : EndoFunctorData R 𝔤}
  {N M : RepGfObj R 𝔤}
  {f : RepGfHom N M}
-- given
  (_hF : IsProjectiveFunctor F)
  (hf : Function.Surjective f.toFun) :
-- imply
  Function.Surjective (F.mapHom f).toFun := by
-- proof
  letI lieRingModulePUnit : LieRingModule 𝔤 PUnit.{u+1} :=
    { bracket := fun _ _ => PUnit.unit
      add_lie := fun _ _ _ => rfl
      lie_add := fun _ _ _ => rfl
      leibniz_lie := fun _ _ _ => by simp }
  letI lieModulePUnit : LieModule R 𝔤 PUnit.{u+1} :=
    { smul_lie := fun _ _ _ => rfl
      lie_smul := fun _ _ _ => rfl }
  let Z : RepGfObj R 𝔤 :=
    { carrier := PUnit
      inst_addCommGroup := inferInstance
      inst_module := inferInstance
      inst_lieRingModule := lieRingModulePUnit
      inst_lieModule := lieModulePUnit }
  haveI : AddCommGroup Z.carrier := Z.inst_addCommGroup
  haveI : Module R Z.carrier := Z.inst_module
  haveI : LieRingModule 𝔤 Z.carrier := Z.inst_lieRingModule
  haveI : LieModule R 𝔤 Z.carrier := Z.inst_lieModule
  let g : RepGfHom M Z := ⟨0⟩
  have hex : IsExactSequence f g := by
    intro m
    constructor
    · intro _
      exact hf m
    · intro _
      exact Subsingleton.elim _ _
  have hFex := _hF.is_exact f g hex
  have hZex : IsExactSequence (RepGfHom.id Z) (RepGfHom.id Z) := by
    intro m
    constructor
    · intro _; exact ⟨m, Subsingleton.elim _ _⟩
    · intro _; exact Subsingleton.elim _ _
  have hFZex := _hF.is_exact (RepGfHom.id Z) (RepGfHom.id Z) hZex
  have hFZ_zero : ∀ (y : (F.obj Z).carrier), y = 0 := by
    intro y
    have hmap_id := F.map_id Z
    have h1 : (F.mapHom (RepGfHom.id Z)).toFun y = y := hmap_id y
    have h2 := (hFZex y).mpr ⟨y, h1⟩
    rwa [h1] at h2
  intro y
  have hgy_zero : (F.mapHom g).toFun y = 0 := hFZ_zero _
  exact (hFex y).mp hgy_zero

end ProjectiveFunctors

namespace ProjectiveFunctors

/--
[IsProjectiveFunctor.toIsProjectiveThetaFunctor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma IsProjectiveFunctor.toIsProjectiveThetaFunctor
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {lam : Δ.𝔥 →ₗ[R] R}
  {F : EndoFunctorData R 𝔤}
-- given
  (hF : IsProjectiveFunctor F) :
-- imply
  IsProjectiveThetaFunctor (hF.toThetaFunctorData Δ wg lam) :=
-- proof
  { exists_tensor_summand := ⟨hF.exists_tensor_summand.choose, hF.exists_tensor_summand.choose_spec⟩ }

end ProjectiveFunctors

namespace ProjectiveFunctors

/--
[idempotent_lift_gives_functor_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma idempotent_lift_gives_functor_decomp
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {F : EndoFunctorData R 𝔤}
  {n : ℕ}
  {E_i : Fin n → NatTransData F F}
  {M₀ : RepGfObj R 𝔤}
  {summands : Fin n → RepGfObj R 𝔤}
-- given
  (_hIdem : ∀ i, ((E_i i).comp (E_i i)).EqPointwise (E_i i))
  (_hDecompObj : IsDirectSumDecompObj (F.obj M₀) summands)
  (_hEvalCompat : ∀ i, ∀ x : (F.obj M₀).carrier, ((E_i i).app M₀).toFun x = (_hDecompObj.choose i).toFun ((_hDecompObj.choose_spec.choose i).toFun x))
  (_hComplete : ∀ (M : RepGfObj R 𝔤) (x : (F.obj M).carrier), x = Finset.univ.sum (fun i => ((E_i i).app M).toFun x)) :
-- imply
  ∃ (F_i : Fin n → EndoFunctorData R 𝔤), (∀ i, (F_i i).obj M₀ = summands i) ∧ IsDirectSumDecomp F F_i := by
-- proof
  let sec_obj := _hDecompObj.choose
  let ret_obj := _hDecompObj.choose_spec.choose
  have hRS_obj := _hDecompObj.choose_spec.choose_spec.1
  have hIdemElt : ∀ i (M : RepGfObj R 𝔤) (x : (F.obj M).carrier),
    ((E_i i).app M).toFun (((E_i i).app M).toFun x) = ((E_i i).app M).toFun x :=
    fun i M x => _hIdem i M x
  classical
  let rangeObj : (i : Fin n) → (M : RepGfObj R 𝔤) → RepGfObj R 𝔤 := fun i M =>
    ⟨↥(((E_i i).app M).toFun.range), inferInstance, inferInstance, inferInstance, inferInstance⟩
  let Fi_obj : (i : Fin n) → RepGfObj R 𝔤 → RepGfObj R 𝔤 := fun i M =>
    if M = M₀ then summands i else rangeObj i M
  have hFi_M₀ : ∀ i, Fi_obj i M₀ = summands i := fun i => if_pos rfl
  suffices hMain : ∃ (F_i : Fin n → EndoFunctorData R 𝔤),
    (∀ i, (F_i i).obj M₀ = summands i) ∧
    (∀ i, ∃ (incl : NatTransData (F_i i) F) (proj : NatTransData F (F_i i)),
      ((proj.comp incl).EqPointwise (NatTransData.id (F_i i))) ∧
      (∀ M x, (incl.app M).toFun ((proj.app M).toFun x) = ((E_i i).app M).toFun x)) by
    obtain ⟨F_i, hObj, hSplit⟩ := hMain
    refine ⟨F_i, hObj, ?_⟩
    let incl_i : ∀ i, NatTransData (F_i i) F := fun i => (hSplit i).choose
    let proj_i : ∀ i, NatTransData F (F_i i) := fun i => (hSplit i).choose_spec.choose
    have hRetract : ∀ i, ((proj_i i).comp (incl_i i)).EqPointwise (NatTransData.id (F_i i)) :=
      fun i => (hSplit i).choose_spec.choose_spec.1
    have hInclProj : ∀ i (M : RepGfObj R 𝔤) (x : (F.obj M).carrier),
      ((incl_i i).app M).toFun (((proj_i i).app M).toFun x) = ((E_i i).app M).toFun x :=
      fun i => (hSplit i).choose_spec.choose_spec.2
    exact ⟨incl_i, proj_i, hRetract,
      fun M x => by
        simp only [RepGfHom.id, LieModuleHom.coe_id, id_eq]
        conv_rhs => arg 2; ext i; rw [hInclProj i M x]
        exact _hComplete M x⟩
  let eqToRepGfHom : ∀ {A B : RepGfObj R 𝔤}, A = B → RepGfHom A B :=
    fun h => h ▸ RepGfHom.id _
  have eqToRepGfHom_symm : ∀ {A B : RepGfObj R 𝔤} (h : A = B) (x : A.carrier),
    (eqToRepGfHom h.symm).toFun ((eqToRepGfHom h).toFun x) = x := by
    intro A B h; subst h; intro x; rfl
  have eqToRepGfHom_symm' : ∀ {A B : RepGfObj R 𝔤} (h : A = B) (x : B.carrier),
    (eqToRepGfHom h).toFun ((eqToRepGfHom h.symm).toFun x) = x := by
    intro A B h; subst h; intro x; rfl
  let myRangeRestrict' : ∀ (i : Fin n) (M : RepGfObj R 𝔤),
    @LieModuleHom R 𝔤 (F.obj M).carrier ↥(((E_i i).app M).toFun.range)
      _ _ (F.obj M).inst_addCommGroup _ (F.obj M).inst_module _
      (F.obj M).inst_lieRingModule _ := fun i M =>
    { toLinearMap := (((E_i i).app M).toFun : (F.obj M).carrier →ₗ[R] (F.obj M).carrier).rangeRestrict
      map_lie' := fun {x m} => by
        apply Subtype.ext
        simp only [LieSubmodule.coe_bracket]
        change ((E_i i).app M).toFun ⁅x, m⁆ = ⁅x, ((E_i i).app M).toFun m⁆
        exact ((E_i i).app M).toFun.map_lie x m }
  have rangeRestrict_incl : ∀ i M (x : (F.obj M).carrier),
    ((((E_i i).app M).toFun.range).incl (myRangeRestrict' i M x) : (F.obj M).carrier) =
    ((E_i i).app M).toFun x := by intro i M x; rfl
  have rangeRestrict_idem : ∀ i M (y : ↥(((E_i i).app M).toFun.range)),
    myRangeRestrict' i M (((E_i i).app M).toFun.range.incl y) = y := by
    intro i M y
    apply Subtype.ext
    change ((E_i i).app M).toFun ↑y = ↑y
    obtain ⟨z, hz⟩ := y.prop
    rw [← hz, hIdemElt i M z]
  let incl_at : ∀ (i : Fin n) (M : RepGfObj R 𝔤), RepGfHom (Fi_obj i M) (F.obj M) :=
    fun i M => if hM : M = M₀ then by
      subst hM
      exact (sec_obj i).comp (eqToRepGfHom (hFi_M₀ i))
    else by
      have h_ne : Fi_obj i M = rangeObj i M := if_neg hM
      exact ⟨(((E_i i).app M).toFun.range.incl).comp (eqToRepGfHom h_ne).toFun⟩
  let proj_at : ∀ (i : Fin n) (M : RepGfObj R 𝔤), RepGfHom (F.obj M) (Fi_obj i M) :=
    fun i M => if hM : M = M₀ then by
      subst hM
      exact (eqToRepGfHom (hFi_M₀ i).symm).comp (ret_obj i)
    else by
      have h_ne : Fi_obj i M = rangeObj i M := if_neg hM
      exact ⟨((eqToRepGfHom h_ne.symm).toFun).comp (myRangeRestrict' i M)⟩
  have incl_proj_eq : ∀ i M (x : (F.obj M).carrier),
    (incl_at i M).toFun ((proj_at i M).toFun x) = ((E_i i).app M).toFun x := by
    intro i M x
    by_cases hM : M = M₀
    · subst hM
      simp only [incl_at, proj_at, dif_pos rfl]
      simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply]
      rw [eqToRepGfHom_symm' (hFi_M₀ i)]
      exact (_hEvalCompat i x).symm
    · simp only [incl_at, proj_at, dif_neg hM]
      simp only [LieModuleHom.coe_comp, Function.comp_apply]
      rw [eqToRepGfHom_symm' (show Fi_obj i M = rangeObj i M from if_neg hM)]
      rfl
  have proj_incl_id : ∀ i M (x : (Fi_obj i M).carrier),
    (proj_at i M).toFun ((incl_at i M).toFun x) = x := by
    intro i M x
    by_cases hM : M = M₀
    · subst hM
      simp only [incl_at, proj_at, dif_pos rfl]
      simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply]
      rw [show (ret_obj i).toFun ((sec_obj i).toFun ((eqToRepGfHom (hFi_M₀ i)).toFun x)) =
        (eqToRepGfHom (hFi_M₀ i)).toFun x from hRS_obj i _]
      exact eqToRepGfHom_symm (hFi_M₀ i) x
    · simp only [incl_at, proj_at, dif_neg hM]
      simp only [LieModuleHom.coe_comp, Function.comp_apply]
      have h_ne : Fi_obj i M = rangeObj i M := if_neg hM
      conv_rhs => rw [← eqToRepGfHom_symm h_ne x]
      congr 1
      exact rangeRestrict_idem i M ((eqToRepGfHom h_ne).toFun x)
  have E_i_nat : ∀ i {M N : RepGfObj R 𝔤} (f : RepGfHom M N) (x : (F.obj M).carrier),
    ((E_i i).app N).toFun ((F.mapHom f).toFun x) =
    (F.mapHom f).toFun (((E_i i).app M).toFun x) := by
    intro i M N f x
    have := (E_i i).naturality f x
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at this
    exact this
  have E_i_fixes_incl : ∀ i M (x : (Fi_obj i M).carrier),
    ((E_i i).app M).toFun ((incl_at i M).toFun x) = (incl_at i M).toFun x := by
    intro i M x
    rw [← incl_proj_eq i M ((incl_at i M).toFun x), proj_incl_id]
  let mapHom_i : ∀ (i : Fin n) {M N : RepGfObj R 𝔤},
    RepGfHom M N → RepGfHom (Fi_obj i M) (Fi_obj i N) := fun i {M} {N} f =>
    (proj_at i N).comp ((F.mapHom f).comp (incl_at i M))
  refine ⟨fun i => ⟨Fi_obj i, @mapHom_i i, ?_, ?_⟩, hFi_M₀, fun i => ?_⟩
  · intro M x
    simp only [RepGfHom.EqAsMap, mapHom_i, RepGfHom.comp, LieModuleHom.coe_comp,
      Function.comp_apply, RepGfHom.id, LieModuleHom.coe_id, id_eq]
    have hFid := F.map_id M ((incl_at i M).toFun x)
    simp only [RepGfHom.id, LieModuleHom.coe_id, id_eq] at hFid
    rw [hFid]
    exact proj_incl_id i M x
  · intro M N P f g x
    simp only [RepGfHom.EqAsMap, mapHom_i, RepGfHom.comp, LieModuleHom.coe_comp,
      Function.comp_apply]
    have hFcomp := F.map_comp f g ((incl_at i M).toFun x)
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hFcomp
    rw [hFcomp]
    congr 1
    rw [incl_proj_eq]
    symm; rw [E_i_nat]
    congr 2
    exact E_i_fixes_incl i M x
  · refine ⟨⟨incl_at i, ?_⟩, ⟨proj_at i, ?_⟩, ?_, ?_⟩
    · intro M₁ M₂ f x
      simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply, mapHom_i]
      rw [incl_proj_eq]
      rw [E_i_nat]
      congr 1
      exact E_i_fixes_incl i M₁ x
    · intro M₁ M₂ f x
      simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply, mapHom_i]
      rw [show (incl_at i M₁).toFun ((proj_at i M₁).toFun x) =
        ((E_i i).app M₁).toFun x from incl_proj_eq i M₁ x]
      conv_lhs => rw [show (proj_at i M₂).toFun ((F.mapHom f).toFun x) =
        (proj_at i M₂).toFun (((E_i i).app M₂).toFun ((F.mapHom f).toFun x)) from by
        rw [← incl_proj_eq i M₂ ((F.mapHom f).toFun x)]
        rw [proj_incl_id]]
      rw [E_i_nat]
    · intro M x
      simp only [NatTransData.comp, NatTransData.id, RepGfHom.comp, RepGfHom.id, RepGfHom.EqAsMap,
        LieModuleHom.coe_comp, Function.comp_apply, LieModuleHom.coe_id, id_eq]
      exact proj_incl_id i M x
    · intro M x
      simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply]
      exact incl_proj_eq i M x

end ProjectiveFunctors

namespace ProjectiveFunctors

/--
[isDirectSummand_trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma isDirectSummand_trans
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {A B C : EndoFunctorData R 𝔤}
-- given
  (h0 : IsDirectSummand A B)
  (h1 : IsDirectSummand B C) :
-- imply
  IsDirectSummand A C := by
-- proof
  obtain ⟨i₁, p₁, hp₁⟩ := h1
  obtain ⟨i₂, p₂, hp₂⟩ := h2
  exact ⟨i₂.comp i₁, p₁.comp p₂, fun M x => by
    simp only [NatTransData.comp, RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply,
      NatTransData.EqPointwise, RepGfHom.EqAsMap, NatTransData.id, RepGfHom.id] at *
    have h2' := hp₂ M ((i₁.app M).toFun x)
    rw [h2']
    exact hp₁ M x⟩

end ProjectiveFunctors

namespace ProjectiveFunctors

/--
[projective_of_direct_summand](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma projective_of_direct_summand
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {F : EndoFunctorData R 𝔤}
  {G : EndoFunctorData R 𝔤}
-- given
  (_hF : IsProjectiveFunctor F)
  (_hSummand : IsDirectSummand G F) :
-- imply
  IsProjectiveFunctor G where exists_tensor_summand := by
-- proof
  obtain ⟨FV, hFV⟩ := _hF.exists_tensor_summand
  exact ⟨FV, isDirectSummand_trans G F FV.functor _hSummand hFV⟩

end ProjectiveFunctors

namespace ProjectiveFunctors

/--
[isDirectSummand_of_isDirectSumDecomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma isDirectSummand_of_isDirectSumDecomp
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {F : EndoFunctorData R 𝔤}
  {n : ℕ}
  {F_i : Fin n → EndoFunctorData R 𝔤}
  {i : Fin n}
-- given
  (h : IsDirectSumDecomp F F_i) :
-- imply
  IsDirectSummand (F_i i) F := by
-- proof
  obtain ⟨sec, ret, hRS, _⟩ := h
  exact ⟨sec i, ret i, hRS i⟩

end ProjectiveFunctors

namespace ProjectiveFunctors

/--
[areNatIso_refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma areNatIso_refl
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {F : EndoFunctorData R 𝔤} :
-- imply
  AreNatIso F F :=
-- proof
  ⟨NatTransData.id F, NatTransData.id F,
    fun M x => by simp [NatTransData.comp, NatTransData.id, RepGfHom.comp, RepGfHom.id],
    fun M x => by simp [NatTransData.comp, NatTransData.id, RepGfHom.comp, RepGfHom.id]⟩

end ProjectiveFunctors

namespace ProjectiveFunctors

/--
[corollary_22_6_iii](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma corollary_22_6_iii
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {theta : Δ.𝔥 →ₗ[R] R}
  {H : ThetaFunctorData R 𝔤 Δ wg theta}
-- given
  (_hH : IsProjectiveThetaFunctor H) :
-- imply
  ∃ (F : EndoFunctorData R 𝔤) (hF : IsProjectiveFunctor F), AreNatIsoTheta H (hF.toThetaFunctorData Δ wg theta) := by
-- proof
  obtain ⟨FV, hDS⟩ := _hH.exists_tensor_summand
  have hF : IsProjectiveFunctor H.baseFunctor :=
    projective_of_direct_summand R 𝔤 FV.functor H.baseFunctor
      (tensor_functor_is_projective FV) hDS
  exact ⟨H.baseFunctor, hF, areNatIso_refl H.baseFunctor⟩

end ProjectiveFunctors

namespace ProjectiveFunctors

/--
[isDirectSumDecomp_to_gen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma isDirectSumDecomp_to_gen
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {F : EndoFunctorData R 𝔤}
  {n : ℕ}
  {F_i : Fin n → EndoFunctorData R 𝔤}
-- given
  (h : IsDirectSumDecomp F F_i) :
-- imply
  @IsDirectSumDecompGen R _ 𝔤 _ _ F (ULift.{u, 0} (Fin n)) (ULift.fintype _) (fun j => F_i j.down) := by
-- proof
  obtain ⟨section_i, retract_i, hRetSec, hSum⟩ := h
  refine ⟨fun j => section_i j.down, fun j => retract_i j.down,
    fun j => hRetSec j.down, ?_⟩
  intro M x
  rw [hSum M x]
  symm
  exact Finset.sum_equiv (Equiv.ulift) (by simp) (by intro i _; rfl)

end ProjectiveFunctors

namespace ProjectiveFunctors

/--
[tensor_finiteDim_categoryO_commring](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma tensor_finiteDim_categoryO_commring
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup V]
  [Module R V]
  [LieRingModule 𝔤 V]
  [LieModule R 𝔤 V]
  [Module.Finite R V]
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  [AddCommGroup VM]
  [Module R VM]
  [LieRingModule 𝔤 VM]
  [LieModule R 𝔤 VM]
  {tensor_iso : VM ≃ₗ⁅R, 𝔤⁆ TensorProduct R V M}
-- given
  (hM : IsCategoryO Δ rd M) :
-- imply
  IsCategoryO Δ rd VM :=
-- proof
  tensor_finiteDim_categoryO hM tensor_iso

end ProjectiveFunctors

namespace ProjectiveFunctors

/--
[tensor_functor_preserves_categoryO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma tensor_functor_preserves_categoryO
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {FV : TensorFunctorData R 𝔤}
  {M : RepGfObj R 𝔤}
-- given
  (hMO : IsCategoryO Δ rd M.carrier) :
-- imply
  IsCategoryO Δ rd (FV.functor.obj M).carrier := by
-- proof
  obtain ⟨iso⟩ := FV.tensor_obj_spec M
  exact @tensor_finiteDim_categoryO_commring R _ 𝔤 _ _ Δ rd
    FV.V FV.inst_addCommGroupV FV.inst_moduleV FV.inst_lieRingModuleV FV.inst_lieModuleV
    FV.inst_finiteDimV
    M.carrier M.inst_addCommGroup M.inst_module M.inst_lieRingModule M.inst_lieModule
    hMO
    (FV.functor.obj M).carrier (FV.functor.obj M).inst_addCommGroup
    (FV.functor.obj M).inst_module (FV.functor.obj M).inst_lieRingModule
    (FV.functor.obj M).inst_lieModule
    iso

end ProjectiveFunctors

namespace ProjectiveFunctors

/--
[tensor_functor_preserves_projectiveInO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma tensor_functor_preserves_projectiveInO
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {FV : TensorFunctorData R 𝔤}
  {M : RepGfObj R 𝔤}
-- given
  (hMO : IsCategoryO Δ rd M.carrier)
  (hMproj : IsProjectiveInO rd M.carrier hMO)
  (hFMO : IsCategoryO Δ rd (FV.functor.obj M).carrier) :
-- imply
  IsProjectiveInO rd (FV.functor.obj M).carrier hFMO := by
-- proof
  obtain ⟨iso⟩ := FV.tensor_obj_spec M
  letI := FV.inst_addCommGroupV
  letI := FV.inst_moduleV
  letI := FV.inst_lieRingModuleV
  letI := FV.inst_lieModuleV
  letI := FV.inst_finiteDimV
  letI := FV.inst_freeV
  exact tensor_projective_in_O (V := FV.V) hMO hMproj hFMO iso

end ProjectiveFunctors

namespace ProjectiveFunctors

/--
[direct_summand_preserves_categoryO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma direct_summand_preserves_categoryO
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {F G : EndoFunctorData R 𝔤}
  {M : RepGfObj R 𝔤}
-- given
  (_hDS : IsDirectSummand F G)
  (hGMO : IsCategoryO Δ rd (G.obj M).carrier) :
-- imply
  IsCategoryO Δ rd (F.obj M).carrier := by
-- proof
  obtain ⟨i_nt, p_nt, hpi⟩ := _hDS
  let sec := (i_nt.app M).toFun
  let ret := (p_nt.app M).toFun
  have hret_sec : ∀ x : (F.obj M).carrier, ret (sec x) = x := hpi M
  exact {
    finitely_generated := by
      obtain ⟨S, hS⟩ := hGMO.finitely_generated
      classical
      refine ⟨S.image ret, ?_⟩
      rw [eq_top_iff]; intro x _
      rw [← hret_sec x]
      have hmem : sec x ∈ LieSubmodule.lieSpan R 𝔤 (↑S : Set (G.obj M).carrier) := by
        rw [hS]; trivial
      apply LieSubmodule.lieSpan_induction R 𝔤 (p := fun y _ =>
        ret y ∈ LieSubmodule.lieSpan R 𝔤 (↑(S.image ret) : Set (F.obj M).carrier))
      · intro m hm
        exact LieSubmodule.subset_lieSpan (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨m, hm, rfl⟩))
      · simp
      · intro a b _ _ ih1 ih2; rw [map_add]; exact add_mem ih1 ih2
      · intro r a _ ih; rw [map_smul]; exact SMulMemClass.smul_mem r ih
      · intro l a _ ih; rw [LieModuleHom.map_lie]; exact LieSubmodule.lie_mem _ ih
      · exact hmem
    weight_decomp := by
      intro m
      obtain ⟨S, v, hv⟩ := hGMO.weight_decomp (sec m)
      refine ⟨S, fun μ => ⟨ret (v μ), fun h => ?_⟩, ?_⟩
      ·
        have hv_wt := (v μ).property h
        rw [← LieModuleHom.map_lie, hv_wt, map_smul]
      ·
        conv_lhs => rw [← hret_sec m, hv]
        rw [map_sum]
    weight_bound := by
      obtain ⟨bds, hbds⟩ := hGMO.weight_bound
      refine ⟨bds, fun μ hμ => ?_⟩
      apply hbds μ
      unfold weights at hμ ⊢
      simp only [Set.mem_setOf_eq] at hμ ⊢
      intro h_contra
      apply hμ
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hsec_x_wt : sec x ∈ WeightSpace Δ (G.obj M).carrier μ := by
        intro h
        rw [← LieModuleHom.map_lie]
        rw [hx h]
        exact map_smul sec (μ h) x
      rw [Submodule.eq_bot_iff] at h_contra
      have hsec_zero : sec x = 0 := h_contra (sec x) hsec_x_wt
      calc x = ret (sec x) := (hret_sec x).symm
        _ = ret 0 := by rw [hsec_zero]
        _ = 0 := map_zero ret
  }

end ProjectiveFunctors

namespace ProjectiveFunctors

/--
[direct_summand_preserves_projectiveInO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma direct_summand_preserves_projectiveInO
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {F G : EndoFunctorData R 𝔤}
  {M : RepGfObj R 𝔤}
-- given
  (_hDS : IsDirectSummand F G)
  (hFMO : IsCategoryO Δ rd (F.obj M).carrier)
  (hGMO : IsCategoryO Δ rd (G.obj M).carrier)
  (hGMproj : IsProjectiveInO rd (G.obj M).carrier hGMO) :
-- imply
  IsProjectiveInO rd (F.obj M).carrier hFMO := by
-- proof
  obtain ⟨i_nt, p_nt, hpi⟩ := _hDS
  let sec := (i_nt.app M).toFun
  let ret := (p_nt.app M).toFun
  have hret_sec : ∀ x : (F.obj M).carrier, ret (sec x) = x := hpi M
  intro X _ _ _ _ hXO N _ _ _ _ hNO f hf g
  let g' : (G.obj M).carrier →ₗ⁅R, 𝔤⁆ N := g.comp ret
  obtain ⟨h', hh'⟩ := hGMproj X hXO N hNO f hf g'
  exact ⟨h'.comp sec, fun x => by
    rw [LieModuleHom.comp_apply, hh']
    show g (ret (sec x)) = g x
    rw [hret_sec x]⟩

end ProjectiveFunctors

namespace ProjectiveFunctors

/--
[projective_functor_preserves_projective_in_O](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma projective_functor_preserves_projective_in_O
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {rd : PositiveRootData Δ}
  {lam : Δ.𝔥 →ₗ[R] R}
  {F : EndoFunctorData R 𝔤}
  {M : RepGfObj R 𝔤}
-- given
  (_hDom : IsDominantWeightLE rd wg lam)
  (_hF : IsProjectiveFunctor F)
  (_hMO : IsCategoryO Δ rd M.carrier)
  (_hMproj : IsProjectiveInO rd M.carrier _hMO) :
-- imply
  ∃ (hFMO : IsCategoryO Δ rd (F.obj M).carrier), IsProjectiveInO rd (F.obj M).carrier hFMO := by
-- proof
  obtain ⟨FV, hDS⟩ := _hF.exists_tensor_summand
  have hFVMO : IsCategoryO Δ rd (FV.functor.obj M).carrier :=
    tensor_functor_preserves_categoryO Δ rd FV M _hMO
  have hFMO : IsCategoryO Δ rd (F.obj M).carrier :=
    direct_summand_preserves_categoryO Δ rd F FV.functor hDS M hFVMO
  have hFVMproj : IsProjectiveInO rd (FV.functor.obj M).carrier hFVMO :=
    tensor_functor_preserves_projectiveInO Δ rd FV M _hMO _hMproj hFVMO
  have hFMproj : IsProjectiveInO rd (F.obj M).carrier hFMO :=
    direct_summand_preserves_projectiveInO Δ rd F FV.functor hDS M hFMO hFVMO hFVMproj
  exact ⟨hFMO, hFMproj⟩

end ProjectiveFunctors

namespace ProjectiveFunctors

/--
[verma_isCategoryO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma verma_isCategoryO
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {wt : Δ.𝔥 →ₗ[R] R}
-- given
  (_hM : IsVermaModule Δ M wt) :
-- imply
  IsCategoryO Δ rd M := by
-- proof
  constructor
  ·
    refine ⟨{_hM.highestWeightVec}, ?_⟩
    simp only [Finset.coe_singleton]
    exact _hM.toIsHighestWeightModule.generates
  ·
    have hwd := _hM.toIsHighestWeightModule.weight_decomposition
    intro m
    have hm : m ∈ (⨆ (μ : Δ.𝔥 →ₗ[R] R), Δ.weightSubspace M μ : Submodule R M) := by
      rw [hwd]; exact Submodule.mem_top
    rw [Submodule.mem_iSup_iff_exists_finset] at hm
    obtain ⟨s, hms⟩ := hm
    rw [Submodule.mem_iSup_finset_iff_exists_sum] at hms
    obtain ⟨v, hv⟩ := hms
    exact ⟨s, fun μ => ⟨(v μ : M), (v μ).prop⟩, hv.symm⟩
  ·
    exact ⟨{wt}, fun μ hμ => ⟨wt, Finset.mem_singleton.mpr rfl,
      _hM.weight_subset_QPlus rd μ hμ⟩⟩
end ProjectiveFunctors


/--
[centerActsByScalar_implies_nilpotentlyShifted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma centerActsByScalar_implies_nilpotentlyShifted_eq
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M : RepGfObj R 𝔤}
  {theta : Δ.𝔥 →ₗ[R] R} :
-- imply
  centerActsByScalar_prop Δ M theta → centerActsNilpotentlyShifted_prop Δ M theta := by
-- proof
  apply ProjectiveFunctors.centerActsByScalar_implies_nilpotentlyShifted Δ M theta

/--
[hasInfChar_implies_hasGenInfChar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma hasInfChar_implies_hasGenInfChar_eq
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M : RepGfObj R 𝔤}
  {theta : Δ.𝔥 →ₗ[R] R}
-- given
  (h : HasInfChar M theta) :
-- imply
  HasGenInfChar M theta := by
-- proof
  apply ProjectiveFunctors.hasInfChar_implies_hasGenInfChar M theta h

/--
[IsProjectiveFunctor.is_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma is_exact_eq
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {F : EndoFunctorData R 𝔤}
  {M₁ M₂ M₃ : RepGfObj R 𝔤}
  {f : RepGfHom M₁ M₂}
  {g : RepGfHom M₂ M₃}
-- given
  (hF : IsProjectiveFunctor F)
  (_hex : IsExactSequence f g) :
-- imply
  IsExactSequence (F.mapHom f) (F.mapHom g) := by
-- proof
  apply ProjectiveFunctors.IsProjectiveFunctor.is_exact hF f g _hex

/--
[IsProjectiveFunctor.sends_projectives_to_projectives](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma sends_projectives_to_projectives_eq
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {F : EndoFunctorData R 𝔤}
  {M : RepGfObj R 𝔤}
-- given
  (hF : IsProjectiveFunctor F)
  (hM : IsProjectiveModule M) :
-- imply
  IsProjectiveModule (F.obj M) := by
-- proof
  apply ProjectiveFunctors.IsProjectiveFunctor.sends_projectives_to_projectives hF M hM

/--
[projective_factors_through_block](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean)
-/
@[path]
private lemma projective_factors_through_block_eq
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {lam : Δ.𝔥 →ₗ[R] R}
  {F : EndoFunctorData R 𝔤}
-- given
  (_hF : IsProjectiveFunctor F) :
-- imply
  FactorsThroughBlock Δ F lam := by
-- proof
  apply ProjectiveFunctors.projective_factors_through_block Δ wg lam F _hF


-- created on 2026-10-23
-- updated on 2026-10-24
