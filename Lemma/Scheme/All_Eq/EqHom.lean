import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma Spec_hom_ext
  {R S : (CommRingCat : Type (u + 1))}
  {g h : Spec S ⟶ Spec R}
  -- given
  (e : g.appTop = h.appTop) :
  -- imply
  g = h := by
  -- proof
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective h
  have h1 := Scheme.ΓSpecIso_naturality φ
  have h2 := Scheme.ΓSpecIso_naturality ψ
  rw [e, h2] at h1
  rw [(cancel_epi (Scheme.ΓSpecIso R).hom).mp h1]

private lemma appLE_of_fac
  {K : Type u} [Field K]
  {X : (Scheme : Type (u + 1))}
  (W : X.Opens)
  (p : Spec (CommRingCat.of K) ⟶ X)
  (p' : Spec (CommRingCat.of K) ⟶ W)
  -- given
  (hfac : p' ≫ W.ι = p)
  (hp : ⊤ ≤ (TopologicalSpace.Opens.map p.base).obj W) :
  -- imply
  p.appLE W ⊤ hp = W.topIso.inv ≫ p'.appTop := by
  -- proof
  subst hfac
  have e2 : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤ (TopologicalSpace.Opens.map p'.base).obj ⊤ := le_top
  rw [← Scheme.Hom.appLE_comp_appLE p' W.ι W ⊤ ⊤ (by rw [Scheme.Opens.ι_preimage_self]) e2,
    Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  congr 1

/--
[AlgebraicGeometry_IsAffineOpen_eq_of_appLE_eq_and_exists_appLE_eq_of_ringHom](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsAffineOpen_eq_of_appLE_eq_and_exists_appLE_eq_of_ringHom.lean)
-/
@[path]
private lemma main
  {K : Type u} [Field K]
  {X : (Scheme : Type (u + 1))}
  (f : X ⟶ Spec (CommRingCat.of K))
  (W : X.Opens)
  -- given
  (hW : IsAffineOpen W) :
  -- imply
  (∀ (p q : Spec (CommRingCat.of K) ⟶ X), p ≫ f = 𝟙 _ → q ≫ f = 𝟙 _ → ∀ (hp : ⊤ ≤ (TopologicalSpace.Opens.map p.base).obj W) (hq : ⊤ ≤ (TopologicalSpace.Opens.map q.base).obj W), p.appLE W ⊤ hp ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom = q.appLE W ⊤ hq ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom → p = q) ∧ (∀ ν : RingHom (X.presheaf.obj (op W)) K, ν.comp ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ W le_top).hom = RingHom.id K → ∃ (p : Spec (CommRingCat.of K) ⟶ X) (_ : p ≫ f = 𝟙 _) (hp : ⊤ ≤ (TopologicalSpace.Opens.map p.base).obj W), (p.appLE W ⊤ hp ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom = ν) := by
  -- proof
  refine ⟨?_, ?_⟩
  ·
    intro p q hpf hqf hp hq hev
    have hpr : Set.range p.base ⊆ Set.range W.ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      apply hp (Set.mem_univ z)
    have hqr : Set.range q.base ⊆ Set.range W.ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      apply hq (Set.mem_univ z)
    have hpfac : IsOpenImmersion.lift W.ι p hpr ≫ W.ι = p := IsOpenImmersion.lift_fac _ _ _
    have hqfac : IsOpenImmersion.lift W.ι q hqr ≫ W.ι = q := IsOpenImmersion.lift_fac _ _ _
    have htop : (IsOpenImmersion.lift W.ι p hpr).appTop = (IsOpenImmersion.lift W.ι q hqr).appTop := by
      have h1 := appLE_of_fac W p _ hpfac hp
      have h2 := appLE_of_fac W q _ hqfac hq
      have h3 : p.appLE W ⊤ hp = q.appLE W ⊤ hq :=
        (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of K)).hom).mp hev
      rw [h1, h2] at h3
      apply (cancel_epi W.topIso.inv).mp h3
    have h4 : IsOpenImmersion.lift W.ι p hpr ≫ hW.isoSpec.hom =
        IsOpenImmersion.lift W.ι q hqr ≫ hW.isoSpec.hom :=
      Spec_hom_ext (by rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, htop])
    rw [← hpfac, ← hqfac, (cancel_mono hW.isoSpec.hom).mp h4]
  ·
    intro ν hν
    have hp : ⊤ ≤ (TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom ν) ≫ hW.fromSpec).base).obj W := by
      intro z _
      change (Spec.map (CommRingCat.ofHom ν) ≫ hW.fromSpec).base z ∈ (W : Set X)
      rw [← hW.range_fromSpec, Scheme.Hom.comp_base, TopCat.coe_comp]
      refine ⟨_, rfl⟩
    have e1 : (⊤ : (Spec (X.presheaf.obj (op W))).Opens) ≤
        (TopologicalSpace.Opens.map hW.fromSpec.base).obj W := by
      rw [hW.fromSpec_preimage_self]
    have e2 : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤
        (TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom ν)).base).obj ⊤ := le_top
    have h1 : hW.fromSpec.appLE W ⊤ e1 = (Scheme.ΓSpecIso (X.presheaf.obj (op W))).inv := by
      rw [Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      convert Category.comp_id _
      apply (congrArg ((Spec (X.presheaf.obj (op W))).presheaf.map ·) (Subsingleton.elim _ _)).trans
        (CategoryTheory.Functor.map_id _ _)
    have h2 : (Spec.map (CommRingCat.ofHom ν)).appLE ⊤ ⊤ e2 = (Spec.map (CommRingCat.ofHom ν)).appTop := by
      simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    have hev : (Spec.map (CommRingCat.ofHom ν) ≫ hW.fromSpec).appLE W ⊤ hp ≫
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom = CommRingCat.ofHom ν := by
      rw [← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ e1 e2, h1, h2, Category.assoc, Scheme.ΓSpecIso_naturality]
      change (Scheme.ΓSpecIso (X.presheaf.obj (op W))).inv ≫ (Scheme.ΓSpecIso (X.presheaf.obj (op W))).hom ≫
        CommRingCat.ofHom ν = _
      rw [Iso.inv_hom_id_assoc]
    refine ⟨Spec.map (CommRingCat.ofHom ν) ≫ hW.fromSpec, ?_, hp, ?_⟩
    ·
      apply Spec_hom_ext
      rw [Scheme.Hom.comp_appTop]
      have h3 : f.appTop ≫ (Spec.map (CommRingCat.ofHom ν) ≫ hW.fromSpec).appTop =
          f.appLE ⊤ W le_top ≫ (Spec.map (CommRingCat.ofHom ν) ≫ hW.fromSpec).appLE W ⊤ hp := by
        rw [Scheme.Hom.appLE_comp_appLE]
        simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
      rw [h3]
      have h4 : (Spec.map (CommRingCat.ofHom ν) ≫ hW.fromSpec).appLE W ⊤ hp =
          CommRingCat.ofHom ν ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv := by
        conv_rhs => rw [← hev]
        simp
      rw [h4]
      have h5 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ W le_top ≫ CommRingCat.ofHom ν = 𝟙 _ := by
        ext a
        apply congrFun (congrArg DFunLike.coe hν) a
      have h6 : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ W le_top) ≫ CommRingCat.ofHom ν = 𝟙 _ := by
        rw [Category.assoc]
        apply h5
      rw [← Category.assoc (f.appLE ⊤ W le_top), ← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of K)).inv,
        ← Category.assoc, ← Category.assoc, h6]
      simp [Scheme.Hom.appTop]
    · apply congrArg CommRingCat.Hom.hom hev


-- created on 2026-10-20
