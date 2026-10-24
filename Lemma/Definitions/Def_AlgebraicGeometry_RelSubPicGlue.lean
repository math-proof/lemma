import Mathlib
import Lemma.Definitions.Def_CategoryTheory_OverTotalPresheaf
import Lemma.Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Lemma.Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf

set_option autoImplicit false

universe w v u

namespace CategoryTheory.Functor

open CategoryTheory Category Opposite

variable {C : Type u} [Category.{v} C] {S : C} {G : (Over S)ᵒᵖ ⥤ Type w}

lemma map_op_map_op_apply_eq_map_op {A B B' : Over S} (k : A ⟶ B) (k' : B ⟶ B') (l : A ⟶ B')
    (h : (k ≫ k').left = l.left) (x : G.obj (op B')) : G.map k.op (G.map k'.op x) = G.map l.op x := by
  rw [map_op_map_op_apply]
  exact map_op_apply_eq_of_left_eq _ _ h x

lemma OverTotal.ofFibre_mk {T : C} (s : T ⟶ S) (x : G.obj (op (Over.mk s))) :
    OverTotal.ofFibre (Over.mk s) x = ⟨s, x⟩ :=
  OverTotal.ext' rfl (map_op_map_op_apply_eq_self _ _ (by simp) _)

variable (G)

theorem overTotal_isSheaf (J : GrothendieckTopology C) [J.Subcanonical]
    (hG : Presieve.IsSheaf (J.over S) G) : Presieve.IsSheaf J G.overTotal := by
  intro T R hR x hx
  have hS : Presieve.IsSheaf J (yoneda.obj S) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  rw [Presieve.compatible_iff_sieveCompatible] at hx

  let x₁ : Presieve.FamilyOfElements (yoneda.obj S) R.arrows := fun T' f hf => (x f hf).1
  have hx₁ : x₁.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro T' T'' f g hf
    change (x (g ≫ f) _).1 = g ≫ (x f hf).1
    rw [hx f g hf]
    rfl
  obtain ⟨t, ht, ht'⟩ := (hS R hR) x₁ hx₁
  have hfst : ∀ {T' : C} (f : T' ⟶ T) (hf : R f), (x f hf).1 = f ≫ t := fun f hf => (ht f hf).symm

  let R' : Sieve (Over.mk t) := (Sieve.overEquiv (Over.mk t)).symm R
  have hR' : R' ∈ (J.over S) (Over.mk t) := J.overEquiv_symm_mem_over _ _ hR
  let y : Presieve.FamilyOfElements G R'.arrows := fun A g hg =>
    OverTotal.toFibre A (x g.left hg) (by rw [hfst]; exact Over.w g)
  have hy : y.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro A A' g k hg
    have hk : (G.overTotal.map k.left.op (x g.left hg)).1 = A'.hom := by
      rw [overTotal_map_fst, Quiver.Hom.unop_op, hfst, ← assoc]
      exact Over.w (k ≫ g)
    calc OverTotal.toFibre A' (x (k ≫ g).left (R'.downward_closed hg k)) _
        = OverTotal.toFibre A' (G.overTotal.map k.left.op (x g.left hg)) hk :=
          OverTotal.toFibre_congr A' (hx g.left k.left hg) _ _
      _ = G.map k.op (OverTotal.toFibre A (x g.left hg) _) := OverTotal.toFibre_naturality k _ _ hk
  obtain ⟨z, hz, hz'⟩ := (hG R' hR') y hy
  refine ⟨⟨t, z⟩, ?_, ?_⟩
  ·
    intro T' f hf
    have hzg := hz (Over.homMk f rfl : Over.mk (f ≫ t) ⟶ Over.mk t) hf
    rw [show G.overTotal.map f.op ⟨t, z⟩ = OverTotal.ofFibre (Over.mk (f ≫ t))
        (G.map (Over.homMk f rfl : Over.mk (f ≫ t) ⟶ Over.mk t).op z) from (OverTotal.ofFibre_mk _ _).symm, hzg]
    exact OverTotal.ofFibre_toFibre _ _ _
  ·
    rintro ⟨t', z'⟩ ha
    obtain rfl : t' = t := ht' t' (fun T' f hf => congrArg Sigma.fst (ha f hf))
    refine Sigma.ext rfl (heq_of_eq ?_)
    apply hz'
    intro A g hg
    have h1 : (G.overTotal.map g.left.op ⟨t', z'⟩).1 = A.hom := by
      rw [overTotal_map_fst]; exact Over.w g
    calc G.map g.op z'
        = OverTotal.toFibre A (G.overTotal.map g.left.op ⟨t', z'⟩) h1 :=
          (map_op_map_op_apply_eq_map_op _ _ _ (by simp) _).symm
      _ = y g hg := OverTotal.toFibre_congr A (ha g.left hg) _ _

end CategoryTheory.Functor

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian Opposite

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {P : SubPicCondition c ε}

noncomputable def designationOfRepresentableBy {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of R)}
    (e : (relSubPicPresheaf c ε P).RepresentableBy (Over.mk p)) : RelativePic0Designation R c where
  P := Y
  toBase := p
  zeroSection := (e.homEquiv.symm
    (⟨relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _)), P.unit_mem _⟩ :
      (relSubPicPresheaf c ε P).obj (op (Over.mk (𝟙 (Spec (CommRingCat.of R))))))).left
  zeroSection_toBase := Over.w _

@[simp] theorem designationOfRepresentableBy_P {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of R)}
    (e : (relSubPicPresheaf c ε P).RepresentableBy (Over.mk p)) : (designationOfRepresentableBy e).P = Y := rfl

@[simp] theorem designationOfRepresentableBy_toBase {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of R)}
    (e : (relSubPicPresheaf c ε P).RepresentableBy (Over.mk p)) : (designationOfRepresentableBy e).toBase = p :=
  rfl

theorem homEquiv_zeroSection_designationOfRepresentableBy {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of R)}
    (e : (relSubPicPresheaf c ε P).RepresentableBy (Over.mk p)) :
    (e.homEquiv (Over.homMk (designationOfRepresentableBy e).zeroSection
        (designationOfRepresentableBy e).zeroSection_toBase :
        Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk p)).1 =
      relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _)) := by
  have h : (Over.homMk (designationOfRepresentableBy e).zeroSection
      (designationOfRepresentableBy e).zeroSection_toBase : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk p) =
      e.homEquiv.symm ⟨relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _)), P.unit_mem _⟩ :=
    Over.OverMorphism.ext rfl
  rw [h, Equiv.apply_symm_apply]

theorem RepresentsRelSubPic.nonempty_of_representableBy' {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of R)}
    (e : (relSubPicPresheaf c ε P).RepresentableBy (Over.mk p)) :
    Nonempty (RepresentsRelSubPic c ε P (designationOfRepresentableBy e)) :=
  RepresentsRelSubPic.nonempty_of_representableBy e (homEquiv_zeroSection_designationOfRepresentableBy e)

theorem RepresentsRelSubPic.nonempty_of_overTotal_representableBy {Y : Scheme.{u}}
    (e : (relSubPicPresheaf c ε P).overTotal.RepresentableBy Y) :
    Nonempty (RepresentsRelSubPic c ε P
      (designationOfRepresentableBy (Functor.RepresentableBy.ofOverTotal e))) :=
  RepresentsRelSubPic.nonempty_of_representableBy' _

noncomputable abbrev relSubPicTotalSheaf
    (hG : Presieve.IsSheaf (Scheme.zariskiTopology.over (Spec (CommRingCat.of R))) (relSubPicPresheaf c ε P)) :
    Sheaf Scheme.zariskiTopology (Type (u + 1)) :=
  ⟨(relSubPicPresheaf c ε P).overTotal,
    (isSheaf_iff_isSheaf_of_type _ _).2 ((relSubPicPresheaf c ε P).overTotal_isSheaf _ hG)⟩

section glue

variable (hG : Presieve.IsSheaf (Scheme.zariskiTopology.over (Spec (CommRingCat.of R))) (relSubPicPresheaf c ε P))
  {ι : Type u} {X : ι → Scheme.{u}}
  (f : ∀ i, uliftYoneda.{u + 1}.obj (X i) ⟶ (relSubPicPresheaf c ε P).overTotal)
  (hf : ∀ i, MorphismProperty.presheafULift.{u + 1} @IsOpenImmersion (f i))
  [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc f)]

noncomputable def gluedDesignation : RelativePic0Designation R c :=
  designationOfRepresentableBy (Functor.RepresentableBy.ofOverTotal
    (Scheme.LocalRepresentabilityULift.representableBy (F := relSubPicTotalSheaf hG) (f := f) hf))

theorem gluedDesignation_P :
    (gluedDesignation hG f hf).P =
      (Scheme.LocalRepresentabilityULift.glueData (F := relSubPicTotalSheaf hG) (f := f) hf).glued := rfl

theorem RepresentsRelSubPic.nonempty_gluedDesignation :
    Nonempty (RepresentsRelSubPic c ε P (gluedDesignation hG f hf)) :=
  RepresentsRelSubPic.nonempty_of_overTotal_representableBy _

instance (i : ι) : IsOpenImmersion
    (Scheme.LocalRepresentabilityULift.toGlued (F := relSubPicTotalSheaf hG) (f := f) hf i :
      X i ⟶ (gluedDesignation hG f hf).P) :=
  inferInstance

end glue

end AlgebraicGeometry.RelPicard
