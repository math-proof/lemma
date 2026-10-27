import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_ext_of_forall_comp_eq_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_ext_of_forall_comp_eq_of_isAlgClosed.lean)
-/
@[path]
private lemma main
  {κ : Type u} [Field κ] [IsAlgClosed κ]
  {X Y : (Scheme : Type (u + 1))}
  (fX : X ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType fX] [IsReduced X]
  (fY : Y ⟶ Spec (CommRingCat.of κ)) [IsSeparated fY]
  {f g : X ⟶ Y}
  (hf : f ≫ fY = fX)
  (hg : g ≫ fY = fX)
  (h : ∀ x : Spec (CommRingCat.of κ) ⟶ X, x ≫ fX = 𝟙 _ → x ≫ f = x ≫ g) :
  f = g := by
  classical
  let _ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace fX
  refine ext_of_fromSpecResidueField_eq f g fY (closedPoints X) ?_ ?_ (hf.trans hg.symm)
  ·
    rw [Dense, ← Set.eq_univ_iff_forall]
    apply closure_closedPoints
  ·
    intro x hx
    have hxcl : IsClosed ({x} : Set X) := hx
    let _ : LocallyOfFiniteType (X.fromSpecResidueField x) := isClosed_singleton_iff_locallyOfFiniteType.1 hxcl
    let _ : LocallyOfFiniteType (X.fromSpecResidueField x ≫ fX) := inferInstance
    set φ : CommRingCat.of κ ⟶ CommRingCat.of (X.residueField x) := Spec.preimage (X.fromSpecResidueField x ≫ fX)
    have hφ : Spec.map φ = X.fromSpecResidueField x ≫ fX := Spec.map_preimage _
    have hft : RingHom.FiniteType φ.hom := by
      have : LocallyOfFiniteType (Spec.map φ) := by
        rw [hφ]
        infer_instance
      apply HasRingHomProperty.Spec_iff.mp this
    let _ : Algebra κ (X.residueField x) := φ.hom.toAlgebra
    let _ : Algebra.FiniteType κ (X.residueField x) := hft
    let _ : Module.Finite κ (X.residueField x) := finite_of_finite_type_of_isJacobsonRing κ (X.residueField x)
    let _ : Algebra.IsIntegral κ (X.residueField x) := inferInstance
    have hbij : Function.Bijective (algebraMap κ (X.residueField x)) := IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : κ ≃+* X.residueField x := RingEquiv.ofBijective (algebraMap κ (X.residueField x)) hbij
    let ψ : CommRingCat.of (X.residueField x) ⟶ CommRingCat.of κ := CommRingCat.ofHom e.symm.toRingHom
    have hψφ : φ ≫ ψ = 𝟙 _ := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      change e.symm (algebraMap κ (X.residueField x) a) = a
      apply e.symm_apply_apply a
    let _ : IsIso ψ := by
      refine ⟨⟨φ, ?_, hψφ⟩⟩
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro b
      change algebraMap κ (X.residueField x) (e.symm b) = b
      apply e.apply_symm_apply b
    let x₀ : Spec (CommRingCat.of κ) ⟶ X := Spec.map ψ ≫ X.fromSpecResidueField x
    have hx₀ : x₀ ≫ fX = 𝟙 _ := by
      change (Spec.map ψ ≫ X.fromSpecResidueField x) ≫ fX = 𝟙 _
      rw [Category.assoc, ← hφ, ← Spec.map_comp, hψφ, Spec.map_id]
    have hx₀' := h x₀ hx₀
    change (Spec.map ψ ≫ X.fromSpecResidueField x) ≫ f = (Spec.map ψ ≫ X.fromSpecResidueField x) ≫ g at hx₀'
    rw [Category.assoc, Category.assoc] at hx₀'
    apply (cancel_epi (Spec.map ψ)).1 hx₀'


-- created on 2026-10-20
