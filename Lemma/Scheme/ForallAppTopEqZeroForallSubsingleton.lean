import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

variable {X Y : (Scheme : Type (u + 1))}

private lemma app_res_top (f : X ⟶ Y) (U : Y.Opens) (s : (Y.presheaf.obj (op ⊤))) :
  (f.app U).hom ((Y.presheaf.map (homOfLE (le_top (a := U))).op).hom s) =
    (X.presheaf.map (homOfLE (le_top (a := ((TopologicalSpace.Opens.map f.base).obj U)))).op).hom
      (f.appTop.hom s) := by
  have h := f.naturality (homOfLE (le_top (a := U))).op
  have h' := congrArg (fun φ => φ.hom s) h
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h'
  rw [h']
  rfl
private lemma appTop_eq_zero_of_forall_app
  (f : X ⟶ Y) (s : (Y.presheaf.obj (op ⊤)))
  (h : ∀ U : Y.affineOpens, (f.app U.1).hom ((Y.presheaf.map (homOfLE (le_top (a := U.1))).op).hom s) = 0) :
  f.appTop.hom s = 0 := by
  let V : Y.affineOpens → X.Opens := fun U => ((TopologicalSpace.Opens.map f.base).obj U.1)
  suffices hcover : (⊤ : X.Opens) ≤ iSup V by
    apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf V ⊤ (fun U => homOfLE le_top) hcover
    intro U
    have hU := h U
    rw [app_res_top] at hU
    apply hU.trans (map_zero _).symm
  intro x _
  obtain ⟨U, hU, hxU⟩ : ∃ U : Y.Opens, IsAffineOpen U ∧ f x ∈ U := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    exact ⟨U, hU, hxU⟩
  rw [Opens.mem_iSup]
  refine ⟨⟨U, hU⟩, hxU⟩
private lemma ofIdealTop_le_ker
  (f : X ⟶ Y) (S : Set (Y.presheaf.obj (op ⊤))) (hS : ∀ s ∈ S, f.appTop.hom s = 0) :
  Scheme.IdealSheafData.ofIdealTop (Ideal.span S) ≤ f.ker := by
  rw [Scheme.Hom.ker, Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U
  rw [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_le_iff_le_comap, Ideal.span_le]
  intro s hs
  rw [SetLike.mem_coe, Ideal.mem_comap, RingHom.mem_ker, app_res_top, hS s hs, map_zero]
private lemma subschemeι_appTop_eq_zero
  (S : Set (Y.presheaf.obj (op ⊤))) (s : (Y.presheaf.obj (op ⊤))) (hs : s ∈ S) :
  (Scheme.IdealSheafData.ofIdealTop (Ideal.span S)).subschemeι.appTop.hom s = 0 := by
  set I := Scheme.IdealSheafData.ofIdealTop (X := Y) (Ideal.span S) with hI
  apply appTop_eq_zero_of_forall_app
  intro U
  have h1 : (Y.presheaf.map (homOfLE (le_top (a := U.1))).op).hom s ∈ I.ideal U := by
    rw [hI, Scheme.IdealSheafData.ofIdealTop_ideal]
    apply Ideal.mem_map_of_mem _ (Ideal.subset_span hs)
  have h2 : I.ideal U ≤ RingHom.ker (I.subschemeι.app U.1).hom := by
    have h := Scheme.Hom.ideal_ker_le I.subschemeι U
    rwa [Scheme.IdealSheafData.ker_subschemeι] at h
  refine h2 h1
private lemma helper_main
  (k : Type u) [Field k] [IsAlgClosed k] {Z : (Scheme : Type (u + 1))} (q : Z ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType q] (S : Set (Z.presheaf.obj (op ⊤)))
  (e : Spec (CommRingCat.of k) ⟶ Z)
  (hart : ∀ {T : (Scheme : Type (u + 1))} [Subsingleton ↥T] (t : T ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t] (x : T ⟶ Z), x ≫ q = t → (∀ s ∈ S, x.appTop.hom s = 0) → x = t ≫ e)
  {T : (Scheme : Type (u + 1))} (t : T ⟶ Spec (CommRingCat.of k)) (x : T ⟶ Z) (hx : x ≫ q = t)
  (hs : ∀ s ∈ S, x.appTop.hom s = 0) :
  x = t ≫ e := by
  set I := Scheme.IdealSheafData.ofIdealTop (X := Z) (Ideal.span S) with hI
  let Z' : (Scheme : Type (u + 1)) := I.subscheme
  let ι' : Z' ⟶ Z := I.subschemeι
  let q' : Z' ⟶ Spec (CommRingCat.of k) := ι' ≫ q
  have hι'S : ∀ s ∈ S, ι'.appTop.hom s = 0 := fun s hs => subschemeι_appTop_eq_zero S s hs
  let _ : JacobsonSpace Z' := LocallyOfFiniteType.jacobsonSpace q'
  have hclosed : ∀ z : Z', IsClosed ({z} : Set Z') → ι' z = e (IsLocalRing.closedPoint k) := by
    intro z hz
    let kz := pointOfClosedPoint q' z hz
    have h1 : (kz ≫ ι') ≫ q = 𝟙 _ := by
      rw [Category.assoc]
      apply pointOfClosedPoint_comp q' z hz
    have h2 : ∀ s ∈ S, (kz ≫ ι').appTop.hom s = 0 := by
      intro s hs
      rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hι'S s hs, map_zero]
    have h3 : kz ≫ ι' = 𝟙 _ ≫ e := hart (𝟙 _) (kz ≫ ι') h1 h2
    rw [Category.id_comp] at h3
    have h4 := congrArg (fun φ : Spec (CommRingCat.of k) ⟶ Z => φ (IsLocalRing.closedPoint k)) h3
    simp only [Scheme.Hom.comp_apply] at h4
    rwa [pointOfClosedPoint_apply] at h4
  let _ : Subsingleton ↥Z' := by
    constructor
    intro z₁ z₂
    have hinj : Function.Injective ι' := ι'.isClosedEmbedding.injective
    have hcp : ∀ c ∈ closedPoints Z', closedPoints Z' = {c} := by
      intro c hc
      ext z
      constructor
      ·
        intro hz
        apply hinj ((hclosed z hz).trans (hclosed c hc).symm)
      ·
        rintro rfl
        apply hc
    have hz₁ : z₁ ∈ closure (closedPoints Z') := by
      rw [closure_closedPoints]
      trivial
    have hz₂ : z₂ ∈ closure (closedPoints Z') := by
      rw [closure_closedPoints]
      trivial
    have hne : (closedPoints Z').Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rwa [h, closure_empty] at hz₁
    obtain ⟨c, hc⟩ := hne
    have hc' : IsClosed ({c} : Set Z') := by
      rw [← mem_closedPoints_iff]
      apply hc
    rw [hcp c hc, hc'.closure_eq] at hz₁ hz₂
    rw [Set.mem_singleton_iff] at hz₁ hz₂
    rw [hz₁, hz₂]
  have hι' : ι' = q' ≫ e := hart q' ι' rfl hι'S
  have hker : ι'.ker ≤ x.ker := by
    show I.subschemeι.ker ≤ x.ker
    rw [Scheme.IdealSheafData.ker_subschemeι]
    apply ofIdealTop_le_ker x S hs
  let x' : T ⟶ Z' := IsClosedImmersion.lift ι' x hker
  have hx' : x' ≫ ι' = x := IsClosedImmersion.lift_fac _ _ _
  calc
    _ = x' ≫ ι' := hx'.symm
    _ = x' ≫ q' ≫ e := by rw [← hι']
    _ = (x' ≫ ι') ≫ q ≫ e := by simp only [q', Category.assoc]
    _ = t ≫ e := by rw [hx', ← Category.assoc, hx]
/--
[AlgebraicGeometry_eq_comp_of_forall_appTop_eq_zero_of_forall_subsingleton](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_eq_comp_of_forall_appTop_eq_zero_of_forall_subsingleton.lean)
-/
@[path]
private lemma main
  (k : Type u) [Field k] [IsAlgClosed k] {Z : (Scheme : Type (u + 1))} (q : Z ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType q] (S : Set (Z.presheaf.obj (op ⊤)))
  (e : Spec (CommRingCat.of k) ⟶ Z)
  (hart : ∀ {T : (Scheme : Type (u + 1))} [Subsingleton ↥T] (t : T ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t] (x : T ⟶ Z), x ≫ q = t → (∀ s ∈ S, x.appTop.hom s = 0) → x = t ≫ e)
  {T : (Scheme : Type (u + 1))} (t : T ⟶ Spec (CommRingCat.of k)) (x : T ⟶ Z) (hx : x ≫ q = t)
  (hs : ∀ s ∈ S, x.appTop.hom s = 0) :
  x = t ≫ e :=
  helper_main k q S e hart t x hx hs


-- created on 2026-10-20
