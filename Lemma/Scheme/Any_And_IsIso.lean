import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma subsingleton_spec_field
  (k : Type u) [Field k] :
    Subsingleton ↥(Spec (CommRingCat.of k)) :=
  ⟨fun p q => PrimeSpectrum.ext (by rw [Ideal.eq_bot_of_prime p.asIdeal, Ideal.eq_bot_of_prime q.asIdeal])⟩
private lemma continuous_of_subsingleton_dom
  {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] [Subsingleton α]
  (m : α → β) :
    Continuous m := by
  rw [continuous_def]
  intro s _
  exact Subsingleton.set_cases (p := fun t : Set α => IsOpen t) isOpen_empty isOpen_univ _
/--
[AlgebraicGeometry_exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_isFinite_of_etale](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_isFinite_of_etale.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k] [IsAlgClosed k] {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of k))
    [IsFinite f] [Etale f] (x : X) :
    ∃ U : X.Opens, (U : Set X) = {x} ∧ IsIso (U.ι ≫ f) := by
  classical
  let _ : Subsingleton ↥(Spec (CommRingCat.of k)) := subsingleton_spec_field k
  let _ : IsAffine X := isAffine_of_isAffineHom f
  have hfin : f.appTop.hom.Finite := f.finite_appTop
  let ι₀ : RingHom k ↑((Spec (CommRingCat.of k)).presheaf.obj (op ⊤)) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hι₀ : Function.Surjective ι₀ :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective
  let φ : RingHom k ↑(X.presheaf.obj (op ⊤)) := f.appTop.hom.comp ι₀
  have hφ : φ.Finite := hfin.comp (RingHom.Finite.of_surjective ι₀ hι₀)
  let hdiscR : DiscreteTopology (PrimeSpectrum ↑(X.presheaf.obj (op ⊤))) := by
    let _ : Algebra k ↑(X.presheaf.obj (op ⊤)) := φ.toAlgebra
    let _ : Module.Finite k ↑(X.presheaf.obj (op ⊤)) := hφ
    let _ : IsArtinianRing ↑(X.presheaf.obj (op ⊤)) := IsArtinianRing.of_finite k _
    infer_instance
  let eX : Homeomorph ↥X (↥(Spec (X.presheaf.obj (op ⊤)))) := Scheme.homeoOfIso X.isoSpec
  let _ : DiscreteTopology ↥(Spec (X.presheaf.obj (op ⊤))) := hdiscR
  let _ : DiscreteTopology ↥X := DiscreteTopology.of_continuous_injective eX.continuous eX.injective
  have hopen : IsOpen ({x} : Set ↥X) := isOpen_discrete _
  let U : X.Opens := ⟨{x}, hopen⟩
  refine ⟨U, rfl, ?_⟩
  set g : ↑U ⟶ Spec (CommRingCat.of k) := U.ι ≫ f with hg
  let _ : Etale g := by
    rw [hg]
    infer_instance
  let _ : FormallyUnramified g := inferInstance
  let _ : LocallyOfFiniteType g := inferInstance
  have hrange : ∀ a : ↥(↑U : (Scheme : Type (u + 1))), U.ι.base a = x := by
    intro a
    have : U.ι.base a ∈ (U : Set ↥X) := by
      rw [← Scheme.Opens.range_ι]
      exact ⟨a, rfl⟩
    exact this
  let _ : Subsingleton ↥(↑U : (Scheme : Type (u + 1))) :=
    ⟨fun a b => U.ι.isOpenEmbedding.injective (by rw [hrange a, hrange b])⟩
  have u₀ : ↥(↑U : (Scheme : Type (u + 1))) := ⟨x, Set.mem_singleton x⟩
  rw [isIso_iff_isIso_stalkMap]
  constructor
  ·
    have hb : Function.Bijective g.base := by
      refine ⟨fun a b _ => Subsingleton.elim a b, fun p => ⟨u₀, Subsingleton.elim _ _⟩⟩
    let h : Homeomorph (↥(↑U : (Scheme : Type (u + 1)))) (↥(Spec (CommRingCat.of k))) :=
      Homeomorph.mk (Equiv.ofBijective g.base hb) g.base.hom.continuous (continuous_of_subsingleton_dom _)
    have : g.base = (TopCat.isoOfHomeo h).hom := by
      ext a
      rfl
    rw [this]
    infer_instance
  ·
    intro u
    let θ : CommRingCat.of k ≅ (Spec (CommRingCat.of k)).presheaf.stalk (g.base u) :=
      (stalkClosedPointIso (CommRingCat.of k)).symm.trans ((Spec (CommRingCat.of k)).presheaf.stalkCongr (Inseparable.of_eq (Subsingleton.elim (IsLocalRing.closedPoint k) (g.base u))))
    let Ψ : CommRingCat.of k ⟶ (↑U : (Scheme : Type (u + 1))).presheaf.stalk u := θ.hom ≫ g.stalkMap u
    suffices hΨ : IsIso Ψ by
      have : g.stalkMap u = θ.inv ≫ Ψ := by simp [Ψ]
      rw [this]
      infer_instance
    let alg₁ : Algebra ↑((Spec (CommRingCat.of k)).presheaf.stalk (g.base u)) ↑((↑U : (Scheme : Type (u + 1))).presheaf.stalk u) :=
      (g.stalkMap u).hom.toAlgebra
    have hEFT : Algebra.EssFiniteType ↑((Spec (CommRingCat.of k)).presheaf.stalk (g.base u)) ↑((↑U : (Scheme : Type (u + 1))).presheaf.stalk u) := by
      rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
      exact LocallyOfFiniteType.stalkMap g u
    have hFU : Algebra.FormallyUnramified ↑((Spec (CommRingCat.of k)).presheaf.stalk (g.base u)) ↑((↑U : (Scheme : Type (u + 1))).presheaf.stalk u) := by
      rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
      exact FormallyUnramified.stalkMap g u
    let alg₀ : Algebra k ↑((Spec (CommRingCat.of k)).presheaf.stalk (g.base u)) := θ.hom.hom.toAlgebra
    let alg₂ : Algebra k ↑((↑U : (Scheme : Type (u + 1))).presheaf.stalk u) := Ψ.hom.toAlgebra
    let _ : IsScalarTower k ↑((Spec (CommRingCat.of k)).presheaf.stalk (g.base u)) ↑((↑U : (Scheme : Type (u + 1))).presheaf.stalk u) :=
      IsScalarTower.of_algebraMap_eq (fun r => rfl)
    have hθsurj : Function.Surjective (algebraMap k ↑((Spec (CommRingCat.of k)).presheaf.stalk (g.base u))) :=
      θ.commRingCatIsoToRingEquiv.surjective
    let _ : Algebra.FiniteType k ↑((Spec (CommRingCat.of k)).presheaf.stalk (g.base u)) :=
      RingHom.FiniteType.of_surjective _ hθsurj
    let _ : Algebra.EssFiniteType k ↑((Spec (CommRingCat.of k)).presheaf.stalk (g.base u)) := inferInstance
    let _ : Algebra.FormallyUnramified k ↑((Spec (CommRingCat.of k)).presheaf.stalk (g.base u)) :=
      Algebra.FormallyUnramified.of_surjective (Algebra.ofId k _) hθsurj
    let _ : Algebra.EssFiniteType k ↑((↑U : (Scheme : Type (u + 1))).presheaf.stalk u) :=
      Algebra.EssFiniteType.comp k ↑((Spec (CommRingCat.of k)).presheaf.stalk (g.base u)) _
    let _ : Algebra.FormallyUnramified k ↑((↑U : (Scheme : Type (u + 1))).presheaf.stalk u) :=
      Algebra.FormallyUnramified.comp k ↑((Spec (CommRingCat.of k)).presheaf.stalk (g.base u)) _
    have hbij := Algebra.FormallyUnramified.bijective_of_isAlgClosed_of_isLocalRing k ↑((↑U : (Scheme : Type (u + 1))).presheaf.stalk u)
    have hΨeq : (algebraMap k ↑((↑U : (Scheme : Type (u + 1))).presheaf.stalk u)) = Ψ.hom := rfl
    rw [hΨeq] at hbij
    apply (RingEquiv.ofBijective Ψ.hom hbij).toCommRingCatIso.isIso_hom


-- created on 2026-10-20
