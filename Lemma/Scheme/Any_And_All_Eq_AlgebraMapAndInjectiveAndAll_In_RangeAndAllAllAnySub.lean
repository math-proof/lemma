import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_Scheme_exists_ringAut_galois_sections_of_free_of_quotient](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_ringAut_galois_sections_of_free_of_quotient.lean)
-/
@[path]
private lemma main
  {X Y : (Scheme : Type (u + 1))} {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X)
    (hadm : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, ((TopologicalSpace.Opens.map ((ρ g).hom).base).obj U) = U)
    (π : X ⟶ Y) (hπ : ∀ g : G, (ρ g).hom ≫ π = π)
    (haff : IsAffineHom π) (hsurj : Function.Surjective π.base)
    (hfib : ∀ x x' : X, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x')
    (hinj : ∀ V : Y.Opens, Function.Injective (π.app V))
    (hrange : ∀ V : Y.Opens, Set.range (π.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (((TopologicalSpace.Opens.map π.base).obj V)) (((TopologicalSpace.Opens.map π.base).obj V)) (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s})
    (hfree : ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ X) (g : G), x ≫ (ρ g).hom = x → g = 1)
    (V : Y.Opens) (hV : IsAffineOpen V) :
    IsAffineOpen (((TopologicalSpace.Opens.map π.base).obj V)) ∧
    let _ : Algebra Y.presheaf.obj (op V) X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V))) := (π.app V).hom.toAlgebra
    ∃ σ : G →* (X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V))) ≃+* X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V)))),
      (∀ (g : G) (a : X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V)))),
        σ g a = (ρ g⁻¹).hom.appLE (((TopologicalSpace.Opens.map π.base).obj V)) (((TopologicalSpace.Opens.map π.base).obj V)) (by rw [← Scheme.Hom.comp_preimage, hπ g⁻¹]) a) ∧
      (∀ (g : G) (r : Y.presheaf.obj (op V)), σ g (algebraMap (Y.presheaf.obj (op V)) X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V))) r) = algebraMap (Y.presheaf.obj (op V)) X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V))) r) ∧
      Function.Injective (algebraMap (Y.presheaf.obj (op V)) X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V)))) ∧
      (∀ a : X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V))), (∀ g : G, σ g a = a) → a ∈ Set.range (algebraMap (Y.presheaf.obj (op V)) X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V))))) ∧
      (∀ P : Ideal X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V))), P.IsPrime → ∀ g : G, g ≠ 1 → ∃ a : X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V))), a - σ g a ∉ P) := by
  classical
  let _ : IsAffineHom π := haff
  have hU : IsAffineOpen (((TopologicalSpace.Opens.map π.base).obj V)) := hV.preimage π
  refine ⟨hU, ?_⟩
  have hle : ∀ g : G, ((TopologicalSpace.Opens.map π.base).obj V) ≤ ((TopologicalSpace.Opens.map ((ρ g).hom).base).obj (((TopologicalSpace.Opens.map π.base).obj V))) := fun g => by
    rw [← Scheme.Hom.comp_preimage, hπ g]
  have keyX : ∀ {f f' : X ⟶ X} (_ : f = f') (e : ((TopologicalSpace.Opens.map π.base).obj V) ≤ ((TopologicalSpace.Opens.map f.base).obj (((TopologicalSpace.Opens.map π.base).obj V)))) (e' : ((TopologicalSpace.Opens.map π.base).obj V) ≤ ((TopologicalSpace.Opens.map f'.base).obj (((TopologicalSpace.Opens.map π.base).obj V)))),
      f.appLE (((TopologicalSpace.Opens.map π.base).obj V)) (((TopologicalSpace.Opens.map π.base).obj V)) e = f'.appLE (((TopologicalSpace.Opens.map π.base).obj V)) (((TopologicalSpace.Opens.map π.base).obj V)) e' := by
    intro f f' h e e'
    subst h
    rfl
  have keyY : ∀ {f f' : X ⟶ Y} (_ : f = f') (e : ((TopologicalSpace.Opens.map π.base).obj V) ≤ ((TopologicalSpace.Opens.map f.base).obj V)) (e' : ((TopologicalSpace.Opens.map π.base).obj V) ≤ ((TopologicalSpace.Opens.map f'.base).obj V)),
      f.appLE V (((TopologicalSpace.Opens.map π.base).obj V)) e = f'.appLE V (((TopologicalSpace.Opens.map π.base).obj V)) e' := by
    intro f f' h e e'
    subst h
    rfl
  let E : G → (X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V))) →+* X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V)))) := fun g =>
    ((ρ g⁻¹).hom.appLE (((TopologicalSpace.Opens.map π.base).obj V)) (((TopologicalSpace.Opens.map π.base).obj V)) (hle g⁻¹)).hom
  have hEdef : ∀ (g : G) (a : X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V)))), E g a = (ρ g⁻¹).hom.appLE (((TopologicalSpace.Opens.map π.base).obj V)) (((TopologicalSpace.Opens.map π.base).obj V)) (hle g⁻¹) a :=
    fun g a => rfl
  have hEmul : ∀ (g h : G) (a : X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V)))), E (g * h) a = E g (E h a) := by
    intro g h a
    rw [hEdef, hEdef, hEdef, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    apply congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _))
      (keyX (by rw [mul_inv_rev, map_mul, Aut.Aut_mul_def, Iso.trans_hom]) _ _)) a
  have hEone : ∀ a : X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V))), E 1 a = a := by
    intro a
    rw [hEdef]
    have hmor : (ρ (1 : G)⁻¹).hom = 𝟙 X := by
      rw [inv_one, map_one]
      rfl
    have e' : ((TopologicalSpace.Opens.map π.base).obj V) ≤ ((TopologicalSpace.Opens.map (𝟙 X : X ⟶ X).base).obj ((TopologicalSpace.Opens.map π.base).obj V)) := by
      rw [Scheme.Hom.id_base, TopologicalSpace.Opens.map_id_obj]
    rw [keyX hmor (hle (1 : G)⁻¹) e']
    have hid : (homOfLE e').op = 𝟙 _ := Subsingleton.elim _ _
    simp only [Scheme.Hom.appLE, hid]
    erw [CategoryTheory.Functor.map_id]
    simp
  have hleft : ∀ g, (E g).comp (E g⁻¹) = RingHom.id _ := by
    intro g
    ext a
    show E g (E g⁻¹ a) = a
    rw [← hEmul, mul_inv_cancel, hEone]
  have hright : ∀ g, (E g⁻¹).comp (E g) = RingHom.id _ := by
    intro g
    ext a
    show E g⁻¹ (E g a) = a
    rw [← hEmul, inv_mul_cancel, hEone]
  let toσ : G → (X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V))) ≃+* X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V)))) :=
    fun g => RingEquiv.ofRingHom (E g) (E g⁻¹) (hleft g) (hright g)
  have hone : toσ 1 = 1 := by
    ext a
    apply hEone a
  have hmul : ∀ g h, toσ (g * h) = toσ g * toσ h := by
    intro g h
    ext a
    apply hEmul g h a
  let σ : G →* (X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V))) ≃+* X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V)))) :=
    { toFun := toσ
      map_one' := hone
      map_mul' := hmul }
  have hσE : ∀ (g : G) (a : X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V)))), σ g a = E g a := fun g a => rfl
  refine ⟨σ, fun g a => rfl, ?_, hinj V, ?_, ?_⟩
  ·
    intro g r
    rw [hσE]
    show E g (π.app V r) = π.app V r
    rw [hEdef, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    exact congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)) (keyY (hπ g⁻¹) _ _)) r
  ·
    intro a ha
    have ha' : ∀ g : G,
        (ρ g).hom.appLE (((TopologicalSpace.Opens.map π.base).obj V)) (((TopologicalSpace.Opens.map π.base).obj V)) (by rw [← Scheme.Hom.comp_preimage, hπ g]) a = a := by
      intro g
      have := ha g⁻¹
      rw [hσE, hEdef] at this
      rw [keyX (show (ρ g).hom = (ρ g⁻¹⁻¹).hom by rw [inv_inv]) _ (hle g⁻¹⁻¹)]
      apply this
    rw [RingHom.algebraMap_toAlgebra (π.app V).hom]
    rwa [hrange V]
  ·
    intro P hP g hg
    by_contra H
    push Not at H
    let _ := hP
    let K : Type u := FractionRing ((X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V)))) ⧸ P)
    let φ₀ : (X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V)))) →+* K := (algebraMap ((X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V)))) ⧸ P) K).comp (Ideal.Quotient.mk P)
    have hφ : φ₀.comp (E g) = φ₀ := by
      ext a
      show algebraMap _ K (Ideal.Quotient.mk P (E g a)) = algebraMap _ K (Ideal.Quotient.mk P a)
      congr 1
      rw [eq_comm, Ideal.Quotient.eq]
      have := H a
      rwa [hσE] at this
    let x : Spec (CommRingCat.of K) ⟶ X := Spec.map (CommRingCat.ofHom φ₀) ≫ hU.fromSpec
    have hx : x ≫ (ρ g⁻¹).hom = x := by
      show (Spec.map (CommRingCat.ofHom φ₀) ≫ hU.fromSpec) ≫ (ρ g⁻¹).hom = Spec.map (CommRingCat.ofHom φ₀) ≫ hU.fromSpec
      rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec (ρ g⁻¹).hom hU hU (hle g⁻¹), ← Category.assoc,
        ← Spec.map_comp]
      congr 2
      ext a
      exact congrFun (congrArg (fun ψ : (X.presheaf.obj (op (((TopologicalSpace.Opens.map π.base).obj V)))) →+* K => (ψ : _ → K)) hφ) a
    have := hfree K x g⁻¹ hx
    exact hg (inv_eq_one.mp this)


-- created on 2026-10-20
