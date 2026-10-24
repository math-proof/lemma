import Mathlib.AlgebraicGeometry.Pullbacks
import Lemma.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Lemma.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian

section Product

variable {R : Type u} [CommRing R] {B C : Scheme.{u}}
  (g : B ⟶ Spec (CommRingCat.of R)) (h : C ⟶ Spec (CommRingCat.of R))

abbrev prodStr : pullback g h ⟶ Spec (CommRingCat.of R) := pullback.fst g h ≫ g

theorem pullback_snd_comp_eq_prodStr : pullback.snd g h ≫ h = prodStr g h :=
  pullback.condition.symm

variable {g h}

section Points

variable {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}

def prodFstPt (z : SchemeHomOver t (prodStr g h)) : SchemeHomOver t g :=
  ⟨z.1 ≫ pullback.fst g h, by rw [Category.assoc]; exact z.2⟩

def prodSndPt (z : SchemeHomOver t (prodStr g h)) : SchemeHomOver t h :=
  ⟨z.1 ≫ pullback.snd g h, by rw [Category.assoc, pullback_snd_comp_eq_prodStr]; exact z.2⟩

def prodPairPt (x : SchemeHomOver t g) (y : SchemeHomOver t h) : SchemeHomOver t (prodStr g h) :=
  ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm), by
    rw [← Category.assoc, pullback.lift_fst]; exact x.2⟩

@[simp] theorem prodFstPt_coe (z : SchemeHomOver t (prodStr g h)) :
    (prodFstPt z).1 = z.1 ≫ pullback.fst g h :=
  rfl

@[simp] theorem prodSndPt_coe (z : SchemeHomOver t (prodStr g h)) :
    (prodSndPt z).1 = z.1 ≫ pullback.snd g h :=
  rfl

@[simp] theorem prodPairPt_coe (x : SchemeHomOver t g) (y : SchemeHomOver t h) :
    (prodPairPt x y).1 = pullback.lift x.1 y.1 (x.2.trans y.2.symm) :=
  rfl

@[simp] theorem prodFstPt_prodPairPt (x : SchemeHomOver t g) (y : SchemeHomOver t h) :
    prodFstPt (prodPairPt x y) = x :=
  Subtype.ext (pullback.lift_fst _ _ _)

@[simp] theorem prodSndPt_prodPairPt (x : SchemeHomOver t g) (y : SchemeHomOver t h) :
    prodSndPt (prodPairPt x y) = y :=
  Subtype.ext (pullback.lift_snd _ _ _)

theorem prodPt_ext {z w : SchemeHomOver t (prodStr g h)} (h1 : prodFstPt z = prodFstPt w)
    (h2 : prodSndPt z = prodSndPt w) : z = w := by
  apply Subtype.ext
  apply pullback.hom_ext
  · exact congrArg Subtype.val h1
  · exact congrArg Subtype.val h2

@[simp] theorem prodPairPt_prodFstPt_prodSndPt (z : SchemeHomOver t (prodStr g h)) :
    prodPairPt (prodFstPt z) (prodSndPt z) = z :=
  prodPt_ext (prodFstPt_prodPairPt _ _) (prodSndPt_prodPairPt _ _)

def prodPointEquiv (t : T ⟶ Spec (CommRingCat.of R)) :
    SchemeHomOver t (prodStr g h) ≃ SchemeHomOver t g × SchemeHomOver t h where
  toFun z := (prodFstPt z, prodSndPt z)
  invFun p := prodPairPt p.1 p.2
  left_inv z := prodPairPt_prodFstPt_prodSndPt z
  right_inv := fun ⟨x, y⟩ => Prod.ext (prodFstPt_prodPairPt x y) (prodSndPt_prodPairPt x y)

theorem prodFstPt_natural {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (z : SchemeHomOver t (prodStr g h)) :
    prodFstPt (schemeHomOverComp ψ hψ z) = schemeHomOverComp ψ hψ (prodFstPt z) :=
  Subtype.ext (Category.assoc _ _ _)

theorem prodSndPt_natural {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (z : SchemeHomOver t (prodStr g h)) :
    prodSndPt (schemeHomOverComp ψ hψ z) = schemeHomOverComp ψ hψ (prodSndPt z) :=
  Subtype.ext (Category.assoc _ _ _)

theorem prodPairPt_natural {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (x : SchemeHomOver t g) (y : SchemeHomOver t h) :
    schemeHomOverComp ψ hψ (prodPairPt x y) =
      prodPairPt (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y) := by
  apply prodPt_ext
  · rw [prodFstPt_natural, prodFstPt_prodPairPt, prodFstPt_prodPairPt]
  · rw [prodSndPt_natural, prodSndPt_prodPairPt, prodSndPt_prodPairPt]

theorem prodFstPt_schemeHomOverComp {S : Scheme.{u}} {s : S ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver s t) (z : SchemeHomOver t (prodStr g h)) :
    prodFstPt (NeronModelInfra.schemeHomOverComp x z) = NeronModelInfra.schemeHomOverComp x (prodFstPt z) :=
  Subtype.ext (Category.assoc _ _ _)

theorem prodSndPt_schemeHomOverComp {S : Scheme.{u}} {s : S ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver s t) (z : SchemeHomOver t (prodStr g h)) :
    prodSndPt (NeronModelInfra.schemeHomOverComp x z) = NeronModelInfra.schemeHomOverComp x (prodSndPt z) :=
  Subtype.ext (Category.assoc _ _ _)

theorem schemeHomOverComp_prodPairPt {S : Scheme.{u}} {s : S ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver s t) (y : SchemeHomOver t g) (z : SchemeHomOver t h) :
    NeronModelInfra.schemeHomOverComp x (prodPairPt y z) =
      prodPairPt (NeronModelInfra.schemeHomOverComp x y) (NeronModelInfra.schemeHomOverComp x z) := by
  apply prodPt_ext
  · rw [prodFstPt_schemeHomOverComp, prodFstPt_prodPairPt, prodFstPt_prodPairPt]
  · rw [prodSndPt_schemeHomOverComp, prodSndPt_prodPairPt, prodSndPt_prodPairPt]

end Points

namespace RelativeGroupLaw

def prod (GB : RelativeGroupLaw R g) (GC : RelativeGroupLaw R h) : RelativeGroupLaw R (prodStr g h) where
  mul t z w := prodPairPt (GB.mul t (prodFstPt z) (prodFstPt w)) (GC.mul t (prodSndPt z) (prodSndPt w))
  one t := prodPairPt (GB.one t) (GC.one t)
  inv t z := prodPairPt (GB.inv t (prodFstPt z)) (GC.inv t (prodSndPt z))
  mul_assoc t x y z := by
    apply prodPt_ext
    · simp only [prodFstPt_prodPairPt, GB.mul_assoc]
    · simp only [prodSndPt_prodPairPt, GC.mul_assoc]
  one_mul t x := by
    apply prodPt_ext
    · simp only [prodFstPt_prodPairPt, GB.one_mul]
    · simp only [prodSndPt_prodPairPt, GC.one_mul]
  mul_one t x := by
    apply prodPt_ext
    · simp only [prodFstPt_prodPairPt, GB.mul_one]
    · simp only [prodSndPt_prodPairPt, GC.mul_one]
  inv_mul_cancel t x := by
    apply prodPt_ext
    · simp only [prodFstPt_prodPairPt, GB.inv_mul_cancel]
    · simp only [prodSndPt_prodPairPt, GC.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    rw [prodPairPt_natural, GB.mul_natural, GC.mul_natural, prodFstPt_natural, prodFstPt_natural,
      prodSndPt_natural, prodSndPt_natural]

variable (GB : RelativeGroupLaw R g) (GC : RelativeGroupLaw R h)

section Unfolding

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

@[simp] theorem prod_mul (z w : SchemeHomOver t (prodStr g h)) :
    (GB.prod GC).mul t z w =
      prodPairPt (GB.mul t (prodFstPt z) (prodFstPt w)) (GC.mul t (prodSndPt z) (prodSndPt w)) :=
  rfl

@[simp] theorem prod_one : (GB.prod GC).one t = prodPairPt (GB.one t) (GC.one t) :=
  rfl

@[simp] theorem prod_inv (z : SchemeHomOver t (prodStr g h)) :
    (GB.prod GC).inv t z = prodPairPt (GB.inv t (prodFstPt z)) (GC.inv t (prodSndPt z)) :=
  rfl

theorem prodFstPt_mul (z w : SchemeHomOver t (prodStr g h)) :
    prodFstPt ((GB.prod GC).mul t z w) = GB.mul t (prodFstPt z) (prodFstPt w) :=
  prodFstPt_prodPairPt _ _

theorem prodSndPt_mul (z w : SchemeHomOver t (prodStr g h)) :
    prodSndPt ((GB.prod GC).mul t z w) = GC.mul t (prodSndPt z) (prodSndPt w) :=
  prodSndPt_prodPairPt _ _

theorem prodPairPt_mul_prodPairPt (x x' : SchemeHomOver t g) (y y' : SchemeHomOver t h) :
    (GB.prod GC).mul t (prodPairPt x y) (prodPairPt x' y') = prodPairPt (GB.mul t x x') (GC.mul t y y') := by
  simp only [prod_mul, prodFstPt_prodPairPt, prodSndPt_prodPairPt]

end Unfolding

theorem IsCommutative.prod {GB : RelativeGroupLaw R g} {GC : RelativeGroupLaw R h} (hB : GB.IsCommutative)
    (hC : GC.IsCommutative) : (GB.prod GC).IsCommutative := by
  intro T t z w
  simp only [prod_mul, hB t (prodFstPt z), hC t (prodSndPt z)]

end RelativeGroupLaw

def prodFst : SchemeHomOver (prodStr g h) g :=
  ⟨pullback.fst g h, rfl⟩

def prodSnd : SchemeHomOver (prodStr g h) h :=
  ⟨pullback.snd g h, pullback_snd_comp_eq_prodStr g h⟩

def prodInl (GC : RelativeGroupLaw R h) : SchemeHomOver g (prodStr g h) :=
  prodPairPt (schemeHomOverId g) (GC.one g)

def prodInr (GB : RelativeGroupLaw R g) : SchemeHomOver h (prodStr g h) :=
  prodPairPt (GB.one h) (schemeHomOverId h)

@[simp] theorem prodFst_coe : (prodFst (g := g) (h := h)).1 = pullback.fst g h := rfl

@[simp] theorem prodSnd_coe : (prodSnd (g := g) (h := h)).1 = pullback.snd g h := rfl

section MapsOnPoints

variable (GB : RelativeGroupLaw R g) (GC : RelativeGroupLaw R h)
variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

theorem schemeHomOverComp_prodFst (z : SchemeHomOver t (prodStr g h)) :
    NeronModelInfra.schemeHomOverComp z (prodFst (g := g) (h := h)) = prodFstPt z :=
  rfl

theorem schemeHomOverComp_prodSnd (z : SchemeHomOver t (prodStr g h)) :
    NeronModelInfra.schemeHomOverComp z (prodSnd (g := g) (h := h)) = prodSndPt z :=
  rfl

theorem schemeHomOverComp_prodInl (x : SchemeHomOver t g) :
    NeronModelInfra.schemeHomOverComp x (prodInl GC) = prodPairPt x (GC.one t) := by
  unfold prodInl
  rw [schemeHomOverComp_prodPairPt, schemeHomOverComp_id_right]
  congr 1
  exact GC.one_natural g t x.1 x.2

theorem schemeHomOverComp_prodInr (y : SchemeHomOver t h) :
    NeronModelInfra.schemeHomOverComp y (prodInr GB) = prodPairPt (GB.one t) y := by
  unfold prodInr
  rw [schemeHomOverComp_prodPairPt, schemeHomOverComp_id_right]
  congr 1
  exact GB.one_natural h t y.1 y.2

theorem prodFst_hom (x y : SchemeHomOver t (prodStr g h)) :
    NeronModelInfra.schemeHomOverComp ((GB.prod GC).mul t x y) (prodFst (g := g) (h := h)) =
      GB.mul t (NeronModelInfra.schemeHomOverComp x prodFst) (NeronModelInfra.schemeHomOverComp y prodFst) := by
  rw [schemeHomOverComp_prodFst, schemeHomOverComp_prodFst, schemeHomOverComp_prodFst,
    RelativeGroupLaw.prodFstPt_mul]

theorem prodSnd_hom (x y : SchemeHomOver t (prodStr g h)) :
    NeronModelInfra.schemeHomOverComp ((GB.prod GC).mul t x y) (prodSnd (g := g) (h := h)) =
      GC.mul t (NeronModelInfra.schemeHomOverComp x prodSnd) (NeronModelInfra.schemeHomOverComp y prodSnd) := by
  rw [schemeHomOverComp_prodSnd, schemeHomOverComp_prodSnd, schemeHomOverComp_prodSnd,
    RelativeGroupLaw.prodSndPt_mul]

theorem prodInl_hom (x y : SchemeHomOver t g) :
    NeronModelInfra.schemeHomOverComp (GB.mul t x y) (prodInl GC) =
      (GB.prod GC).mul t (NeronModelInfra.schemeHomOverComp x (prodInl GC))
        (NeronModelInfra.schemeHomOverComp y (prodInl GC)) := by
  rw [schemeHomOverComp_prodInl, schemeHomOverComp_prodInl, schemeHomOverComp_prodInl,
    RelativeGroupLaw.prodPairPt_mul_prodPairPt, GC.one_mul]

theorem prodInr_hom (x y : SchemeHomOver t h) :
    NeronModelInfra.schemeHomOverComp (GC.mul t x y) (prodInr GB) =
      (GB.prod GC).mul t (NeronModelInfra.schemeHomOverComp x (prodInr GB))
        (NeronModelInfra.schemeHomOverComp y (prodInr GB)) := by
  rw [schemeHomOverComp_prodInr, schemeHomOverComp_prodInr, schemeHomOverComp_prodInr,
    RelativeGroupLaw.prodPairPt_mul_prodPairPt, GB.one_mul]

theorem prodPairPt_hom {X : Scheme.{u}} {e : X ⟶ Spec (CommRingCat.of R)} (GX : RelativeGroupLaw R e)
    (u : SchemeHomOver e g) (v : SchemeHomOver e h)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t e),
      NeronModelInfra.schemeHomOverComp (GX.mul t x y) u =
        GB.mul t (NeronModelInfra.schemeHomOverComp x u) (NeronModelInfra.schemeHomOverComp y u))
    (hv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t e),
      NeronModelInfra.schemeHomOverComp (GX.mul t x y) v =
        GC.mul t (NeronModelInfra.schemeHomOverComp x v) (NeronModelInfra.schemeHomOverComp y v))
    (x y : SchemeHomOver t e) :
    NeronModelInfra.schemeHomOverComp (GX.mul t x y) (prodPairPt u v) =
      (GB.prod GC).mul t (NeronModelInfra.schemeHomOverComp x (prodPairPt u v))
        (NeronModelInfra.schemeHomOverComp y (prodPairPt u v)) := by
  rw [schemeHomOverComp_prodPairPt, schemeHomOverComp_prodPairPt, schemeHomOverComp_prodPairPt,
    RelativeGroupLaw.prodPairPt_mul_prodPairPt, hu, hv]

theorem prodPt_eq_mul_prodInl_prodInr (z : SchemeHomOver t (prodStr g h)) :
    z = (GB.prod GC).mul t (NeronModelInfra.schemeHomOverComp (prodFstPt z) (prodInl GC))
      (NeronModelInfra.schemeHomOverComp (prodSndPt z) (prodInr GB)) := by
  rw [schemeHomOverComp_prodInl, schemeHomOverComp_prodInr, RelativeGroupLaw.prodPairPt_mul_prodPairPt,
    GB.mul_one, GC.one_mul, prodPairPt_prodFstPt_prodSndPt]

end MapsOnPoints

section Identities

variable (GB : RelativeGroupLaw R g) (GC : RelativeGroupLaw R h)

@[simp] theorem prodInl_comp_prodFst :
    NeronModelInfra.schemeHomOverComp (prodInl GC) prodFst = schemeHomOverId g := by
  rw [schemeHomOverComp_prodFst]; exact prodFstPt_prodPairPt _ _

@[simp] theorem prodInl_comp_prodSnd :
    NeronModelInfra.schemeHomOverComp (prodInl GC) prodSnd = GC.one g := by
  rw [schemeHomOverComp_prodSnd]; exact prodSndPt_prodPairPt _ _

@[simp] theorem prodInr_comp_prodFst :
    NeronModelInfra.schemeHomOverComp (prodInr GB) prodFst = GB.one h := by
  rw [schemeHomOverComp_prodFst]; exact prodFstPt_prodPairPt _ _

@[simp] theorem prodInr_comp_prodSnd :
    NeronModelInfra.schemeHomOverComp (prodInr (g := g) GB) prodSnd = schemeHomOverId h := by
  rw [schemeHomOverComp_prodSnd]; exact prodSndPt_prodPairPt _ _

theorem prod_mul_prodFst_prodInl_prodSnd_prodInr :
    (GB.prod GC).mul (prodStr g h) (NeronModelInfra.schemeHomOverComp prodFst (prodInl GC))
      (NeronModelInfra.schemeHomOverComp prodSnd (prodInr GB)) = schemeHomOverId (prodStr g h) := by
  rw [schemeHomOverComp_prodInl, schemeHomOverComp_prodInr, RelativeGroupLaw.prodPairPt_mul_prodPairPt,
    GB.mul_one, GC.one_mul]
  apply prodPt_ext
  · rw [prodFstPt_prodPairPt]; rfl
  · rw [prodSndPt_prodPairPt]; rfl

theorem eq_one_of_prodInl_comp_of_prodInr_comp (β : SchemeHomOver (prodStr g h) (prodStr g h))
    (hβ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (prodStr g h)),
      NeronModelInfra.schemeHomOverComp ((GB.prod GC).mul t x y) β =
        (GB.prod GC).mul t (NeronModelInfra.schemeHomOverComp x β) (NeronModelInfra.schemeHomOverComp y β))
    (h1 : NeronModelInfra.schemeHomOverComp (prodInl GC) β = (GB.prod GC).one g)
    (h2 : NeronModelInfra.schemeHomOverComp (prodInr GB) β = (GB.prod GC).one h) :
    β = (GB.prod GC).one (prodStr g h) := by
  have key : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (z : SchemeHomOver t (prodStr g h)),
      NeronModelInfra.schemeHomOverComp z β = (GB.prod GC).one t := by
    intro T t z
    rw [prodPt_eq_mul_prodInl_prodInr GB GC t z, hβ, schemeHomOverComp_assoc, schemeHomOverComp_assoc, h1, h2]
    have e1 : NeronModelInfra.schemeHomOverComp (prodFstPt z) ((GB.prod GC).one g) = (GB.prod GC).one t :=
      (GB.prod GC).one_natural g t (prodFstPt z).1 (prodFstPt z).2
    have e2 : NeronModelInfra.schemeHomOverComp (prodSndPt z) ((GB.prod GC).one h) = (GB.prod GC).one t :=
      (GB.prod GC).one_natural h t (prodSndPt z).1 (prodSndPt z).2
    rw [e1, e2, (GB.prod GC).one_mul]
  have := key (prodStr g h) (schemeHomOverId (prodStr g h))
  rwa [schemeHomOverComp_id_left] at this

theorem eq_one_of_prod_entries_eq_one (β : SchemeHomOver (prodStr g h) (prodStr g h))
    (hβ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (prodStr g h)),
      NeronModelInfra.schemeHomOverComp ((GB.prod GC).mul t x y) β =
        (GB.prod GC).mul t (NeronModelInfra.schemeHomOverComp x β) (NeronModelInfra.schemeHomOverComp y β))
    (h11 : NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (prodInl GC) β) prodFst = GB.one g)
    (h12 : NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (prodInl GC) β) prodSnd = GC.one g)
    (h21 : NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (prodInr GB) β) prodFst = GB.one h)
    (h22 : NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (prodInr GB) β) prodSnd = GC.one h) :
    β = (GB.prod GC).one (prodStr g h) := by
  refine eq_one_of_prodInl_comp_of_prodInr_comp GB GC β hβ ?_ ?_
  · apply prodPt_ext
    · rw [← schemeHomOverComp_prodFst, h11, RelativeGroupLaw.prod_one, prodFstPt_prodPairPt]
    · rw [← schemeHomOverComp_prodSnd, h12, RelativeGroupLaw.prod_one, prodSndPt_prodPairPt]
  · apply prodPt_ext
    · rw [← schemeHomOverComp_prodFst, h21, RelativeGroupLaw.prod_one, prodFstPt_prodPairPt]
    · rw [← schemeHomOverComp_prodSnd, h22, RelativeGroupLaw.prod_one, prodSndPt_prodPairPt]

end Identities

end Product

theorem schemeHomOver_eq_of_epi_comp {R : Type u} [CommRing R] {X A A' : Scheme.{u}}
    {e : X ⟶ Spec (CommRingCat.of R)} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (σ : SchemeHomOver e f) [Epi σ.1] (β γ : SchemeHomOver f f')
    (hσ : NeronModelInfra.schemeHomOverComp σ β = NeronModelInfra.schemeHomOverComp σ γ) : β = γ := by
  apply Subtype.ext
  have h1 := congrArg Subtype.val hσ
  simp only [NeronModelInfra.schemeHomOverComp_coe] at h1
  exact (cancel_epi σ.1).mp h1

end GoodReductionJacobian

end
