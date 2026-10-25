import Lemma.AlgebraicGeometry.RelativeGroupLaw
import Def.AlgebraicGeometry_RelativeGroupLawGrpObj

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory NeronModelInfra

open scoped CategoryTheory.MonObj

namespace GoodReductionJacobian


@[simp]
theorem overHomEquivSchemeHomOver_apply_coe {R : Type u} [CommRing R] {A : Scheme.{u}}
    (T : Over (Spec (CommRingCat.of R))) (f : A ⟶ Spec (CommRingCat.of R))
    (φ : T ⟶ Over.mk f) : (overHomEquivSchemeHomOver T f φ).1 = φ.left :=
  rfl

@[simp]
theorem overHomEquivSchemeHomOver_symm_apply_left {R : Type u} [CommRing R] {A : Scheme.{u}}
    (T : Over (Spec (CommRingCat.of R))) (f : A ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver T.hom f) : ((overHomEquivSchemeHomOver T f).symm x).left = x.1 :=
  rfl

theorem overHomEquivSchemeHomOver_mk_apply {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (h : Over.mk t ⟶ Over.mk f) :
    overHomEquivSchemeHomOver (Over.mk t) f h = overHomToSchemeHomOver h :=
  rfl

theorem overHomEquivSchemeHomOver_mk_symm_apply {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    (overHomEquivSchemeHomOver (Over.mk t) f).symm x = schemeHomOverToOverHom x :=
  rfl

theorem overHomToSchemeHomOver_injective {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} :
    Function.Injective
      (overHomToSchemeHomOver : (Over.mk t ⟶ Over.mk f) → SchemeHomOver t f) := by
  intro a b h
  have h2 := congrArg schemeHomOverToOverHom h
  simpa using h2


@[simp]
theorem relativeGroupLawOfGrpObj_mul {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)] {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    (relativeGroupLawOfGrpObj R f).mul t x y =
      overHomToSchemeHomOver (schemeHomOverToOverHom x * schemeHomOverToOverHom y) :=
  rfl

@[simp]
theorem relativeGroupLawOfGrpObj_one {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)] {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    (relativeGroupLawOfGrpObj R f).one t =
      overHomToSchemeHomOver (1 : Over.mk t ⟶ Over.mk f) :=
  rfl

@[simp]
theorem relativeGroupLawOfGrpObj_inv {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)] {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    (relativeGroupLawOfGrpObj R f).inv t x =
      overHomToSchemeHomOver (schemeHomOverToOverHom x)⁻¹ :=
  rfl


theorem RelativeGroupLaw.overHomToSchemeHomOver_mul {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (a b : Over.mk t ⟶ Over.mk f) :
    letI := G.grpObjOverMk
    overHomToSchemeHomOver (a * b) =
      G.mul t (overHomToSchemeHomOver a) (overHomToSchemeHomOver b) := by
  letI := G.grpObjOverMk
  exact ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op (Over.mk t))).hom.map_mul a b

theorem RelativeGroupLaw.overHomToSchemeHomOver_one {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    letI := G.grpObjOverMk
    overHomToSchemeHomOver (1 : Over.mk t ⟶ Over.mk f) = G.one t := by
  letI := G.grpObjOverMk
  exact ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op (Over.mk t))).hom.map_one

theorem RelativeGroupLaw.overHomToSchemeHomOver_inv {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (a : Over.mk t ⟶ Over.mk f) :
    letI := G.grpObjOverMk
    overHomToSchemeHomOver a⁻¹ = G.inv t (overHomToSchemeHomOver a) := by
  letI := G.grpObjOverMk
  letI := G.pointGroup t
  exact map_inv ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op (Over.mk t))).hom a

theorem RelativeGroupLaw.overHomEquivSchemeHomOver_mul {R : Type u} [CommRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (T : Over (Spec (CommRingCat.of R))) (a b : T ⟶ Over.mk f) :
    letI := G.grpObjOverMk
    overHomEquivSchemeHomOver T f (a * b) =
      G.mul T.hom (overHomEquivSchemeHomOver T f a) (overHomEquivSchemeHomOver T f b) := by
  letI := G.grpObjOverMk
  exact ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op T)).hom.map_mul a b

theorem RelativeGroupLaw.overHomEquivSchemeHomOver_one {R : Type u} [CommRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (T : Over (Spec (CommRingCat.of R))) :
    letI := G.grpObjOverMk
    overHomEquivSchemeHomOver T f (1 : T ⟶ Over.mk f) = G.one T.hom := by
  letI := G.grpObjOverMk
  exact ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op T)).hom.map_one

theorem RelativeGroupLaw.overHomEquivSchemeHomOver_inv {R : Type u} [CommRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (T : Over (Spec (CommRingCat.of R))) (a : T ⟶ Over.mk f) :
    letI := G.grpObjOverMk
    overHomEquivSchemeHomOver T f a⁻¹ = G.inv T.hom (overHomEquivSchemeHomOver T f a) := by
  letI := G.grpObjOverMk
  letI := G.pointGroup T.hom
  exact map_inv ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op T)).hom a

theorem RelativeGroupLaw.grpObjOverMk_mul_eq {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    letI := G.grpObjOverMk
    overHomEquivSchemeHomOver (Over.mk f ⊗ Over.mk f) f μ[Over.mk f] =
      G.mul (Over.mk f ⊗ Over.mk f).hom
        (overHomEquivSchemeHomOver (Over.mk f ⊗ Over.mk f) f (fst (Over.mk f) (Over.mk f)))
        (overHomEquivSchemeHomOver (Over.mk f ⊗ Over.mk f) f (snd (Over.mk f) (Over.mk f))) := by
  letI := G.grpObjOverMk
  rw [MonObj.mul_eq_mul]
  exact G.overHomEquivSchemeHomOver_mul (Over.mk f ⊗ Over.mk f)
    (fst (Over.mk f) (Over.mk f)) (snd (Over.mk f) (Over.mk f))

theorem RelativeGroupLaw.grpObjOverMk_one_eq {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    letI := G.grpObjOverMk
    overHomEquivSchemeHomOver (𝟙_ (Over (Spec (CommRingCat.of R)))) f η[Over.mk f] =
      G.one (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := by
  letI := G.grpObjOverMk
  rw [MonObj.one_eq_one]
  exact G.overHomEquivSchemeHomOver_one (𝟙_ (Over (Spec (CommRingCat.of R))))

theorem RelativeGroupLaw.grpObjOverMk_inv_eq {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    letI := G.grpObjOverMk
    overHomEquivSchemeHomOver (Over.mk f) f ι[Over.mk f] =
      G.inv (Over.mk f).hom (overHomEquivSchemeHomOver (Over.mk f) f (𝟙 (Over.mk f))) := by
  letI := G.grpObjOverMk
  rw [GrpObj.inv_eq_inv]
  exact G.overHomEquivSchemeHomOver_inv (Over.mk f) (𝟙 (Over.mk f))

theorem relativeGroupLawOfGrpObj_grpObjOverMk_mul {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    letI := G.grpObjOverMk
    (relativeGroupLawOfGrpObj R f).mul t x y = G.mul t x y := by
  letI := G.grpObjOverMk
  have h := G.overHomToSchemeHomOver_mul t (schemeHomOverToOverHom x)
    (schemeHomOverToOverHom y)
  simpa using h

theorem relativeGroupLawOfGrpObj_grpObjOverMk_one {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    letI := G.grpObjOverMk
    (relativeGroupLawOfGrpObj R f).one t = G.one t := by
  letI := G.grpObjOverMk
  exact G.overHomToSchemeHomOver_one t

theorem relativeGroupLawOfGrpObj_grpObjOverMk_inv {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    letI := G.grpObjOverMk
    (relativeGroupLawOfGrpObj R f).inv t x = G.inv t x := by
  letI := G.grpObjOverMk
  have h := G.overHomToSchemeHomOver_inv t (schemeHomOverToOverHom x)
  simpa using h

theorem relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj {R : Type u} [CommRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)]
    (h : IsCommMonObj (Over.mk f)) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t f) :
    (relativeGroupLawOfGrpObj R f).mul t x y = (relativeGroupLawOfGrpObj R f).mul t y x := by
  haveI := (isCommMonObj_iff_isMulCommutative (Over.mk f)).mp h (Over.mk t)
  show overHomToSchemeHomOver (schemeHomOverToOverHom x * schemeHomOverToOverHom y) =
    overHomToSchemeHomOver (schemeHomOverToOverHom y * schemeHomOverToOverHom x)
  rw [mul_comm]

theorem isCommMonObj_of_relativeGroupLawOfGrpObj_comm {R : Type u} [CommRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)]
    (hc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      (relativeGroupLawOfGrpObj R f).mul t x y = (relativeGroupLawOfGrpObj R f).mul t y x) :
    IsCommMonObj (Over.mk f) := by
  rw [isCommMonObj_iff_isMulCommutative]
  intro X
  constructor
  constructor
  intro a b
  have h := hc X.hom (overHomToSchemeHomOver a) (overHomToSchemeHomOver b)
  show a * b = b * a
  simp only [relativeGroupLawOfGrpObj, schemeHomOverToOverHom_overHomToSchemeHomOver] at h
  exact overHomToSchemeHomOver_injective h

theorem isCommMonObj_iff_relativeGroupLawOfGrpObj_comm {R : Type u} [CommRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)] :
    IsCommMonObj (Over.mk f) ↔
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        (relativeGroupLawOfGrpObj R f).mul t x y = (relativeGroupLawOfGrpObj R f).mul t y x :=
  ⟨fun h _ _ x y => relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj h _ x y,
    fun hc => isCommMonObj_of_relativeGroupLawOfGrpObj_comm fun t x y => hc t x y⟩

theorem RelativeGroupLaw.isCommMonObj_grpObjOverMk_iff_mul_comm {R : Type u} [CommRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    (letI := G.grpObjOverMk; IsCommMonObj (Over.mk f)) ↔
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        G.mul t x y = G.mul t y x := by
  letI := G.grpObjOverMk
  constructor
  · intro h T t x y
    rw [← relativeGroupLawOfGrpObj_grpObjOverMk_mul G t x y,
      ← relativeGroupLawOfGrpObj_grpObjOverMk_mul G t y x]
    exact relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj h t x y
  · intro hc
    rw [isCommMonObj_iff_isMulCommutative]
    intro X
    constructor
    constructor
    intro a b
    apply (overHomEquivSchemeHomOver X f).injective
    rw [G.overHomEquivSchemeHomOver_mul X a b, G.overHomEquivSchemeHomOver_mul X b a]
    exact hc X.hom _ _

theorem RelativeGroupLaw.mul_comm_of_isProper_of_geometricallyIntegral {K : Type u} [Field K]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)} [IsProper f] [GeometricallyIntegral f]
    (G : RelativeGroupLaw K f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t f) :
    G.mul t x y = G.mul t y x := by
  haveI : IsProper (Over.mk f).hom := ‹IsProper f›
  haveI : GeometricallyIntegral (Over.mk f).hom := ‹GeometricallyIntegral f›
  letI := G.grpObjOverMk
  haveI hcomm : IsCommMonObj (Over.mk f) :=
    isCommMonObj_of_isProper_of_geometricallyIntegral (Over.mk f)
  exact G.isCommMonObj_grpObjOverMk_iff_mul_comm.mp hcomm t x y

end GoodReductionJacobian

end
