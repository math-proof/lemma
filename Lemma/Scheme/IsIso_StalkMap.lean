import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma stalkSpecializes_injective
  {X : (Scheme : Type (u + 1))} [IsIntegral X]
  {x y : X}
  -- given
  (h : x ⤳ y) :
  -- imply
  Function.Injective (X.presheaf.stalkSpecializes h) := by
  -- proof
  have hgx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hcomp : X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes hgx =
      X.presheaf.stalkSpecializes (hgx.trans h) := TopCat.Presheaf.stalkSpecializes_comp _ _ _
  have hinj : Function.Injective (X.presheaf.stalkSpecializes (hgx.trans h)) := by
    change Function.Injective (algebraMap (X.presheaf.stalk y) X.functionField)
    apply IsFractionRing.injective
  have hinj' : Function.Injective ((X.presheaf.stalkSpecializes hgx) ∘ (X.presheaf.stalkSpecializes h)) := by
    intro a b hab
    apply hinj
    change (X.presheaf.stalkSpecializes (hgx.trans h)) a = (X.presheaf.stalkSpecializes (hgx.trans h)) b
    rw [← hcomp]
    apply hab
  refine hinj'.of_comp

private lemma exists_frac
  {G : (Scheme : Type (u + 1))} [IsIntegral G]
  (y z : G)
  (k : G.presheaf.stalk y)
  -- given
  (hy : y = genericPoint G)
  (h : y ⤳ z) :
  -- imply
  ∃ r s : G.presheaf.stalk z, s ≠ 0 ∧ k * G.presheaf.stalkSpecializes h s = G.presheaf.stalkSpecializes h r := by
  -- proof
  subst hy
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors (G.presheaf.stalk z)) (S := G.functionField) k
  refine ⟨r, s.1, nonZeroDivisors.ne_zero s.2, ?_⟩
  apply hrs

private lemma stalkMap_dvr
  {Γ G : (Scheme : Type (u + 1))} [IsIntegral Γ] [IsIntegral G]
  (π : Γ ⟶ G)
  (γ : Γ) [IsDiscreteValuationRing (G.presheaf.stalk (π.base γ))]
  -- given
  (hgen : π.base (genericPoint Γ) = genericPoint G)
  (hbir : IsIso (π.stalkMap (genericPoint Γ))) :
  -- imply
  IsIso (π.stalkMap γ) := by
  -- proof
  set R := G.presheaf.stalk (π.base γ) with hR
  set A := Γ.presheaf.stalk γ with hA
  let φ : RingHom R A := (π.stalkMap γ).hom
  have hξγ : genericPoint Γ ⤳ γ := (genericPoint_spec Γ).specializes trivial
  let ι : RingHom A Γ.functionField := (Γ.presheaf.stalkSpecializes hξγ).hom
  have hι : Function.Injective ι := stalkSpecializes_injective hξγ
  let sp : RingHom R (G.presheaf.stalk (π.base (genericPoint Γ))) :=
    (G.presheaf.stalkSpecializes (π.base.hom.map_specializes hξγ)).hom
  let ψ : RingHom (G.presheaf.stalk (π.base (genericPoint Γ))) Γ.functionField := (π.stalkMap (genericPoint Γ)).hom
  have hsq : ∀ r : R, ψ (sp r) = ι (φ r) := fun r =>
    Scheme.Hom.stalkSpecializes_stalkMap_apply π (genericPoint Γ) γ hξγ r
  have hψ : Function.Bijective ψ := ConcreteCategory.bijective_of_isIso (π.stalkMap (genericPoint Γ))
  have hsp : Function.Injective sp := stalkSpecializes_injective _
  have hinj : Function.Injective φ := by
    intro a b hab
    apply hsp
    apply hψ.1
    rw [hsq, hsq, hab]
  have hfrac : ∀ a : A, ∃ r s : R, s ≠ 0 ∧ a * φ s = φ r := by
    intro a
    obtain ⟨k, hk⟩ := hψ.2 (ι a)
    obtain ⟨r, s, hs, hrs⟩ := exists_frac (π.base (genericPoint Γ)) (π.base γ) k hgen
      (π.base.hom.map_specializes hξγ)
    refine ⟨r, s, hs, hι ?_⟩
    rw [map_mul, ← hsq, ← hsq, ← hk]
    change ψ k * ψ (sp s) = ψ (sp r)
    rw [← map_mul]
    apply congrArg ψ hrs
  have hsurj : Function.Surjective φ := by
    intro a
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨r, s, hs, hrs⟩ := hfrac a
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs hϖ
    if hr : r = 0 then
      subst hr
      rw [map_zero] at hrs
      have hφs : φ ((u : R) * ϖ ^ n) ≠ 0 := fun h0 => hs (hinj (h0.trans (map_zero φ).symm))
      refine ⟨0, ?_⟩
      rw [map_zero]
      apply ((mul_eq_zero.mp hrs).resolve_right hφs).symm
    else
      obtain ⟨m, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
      have hϖA : φ ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hinj (h0.trans (map_zero φ).symm))
      obtain hmn | hnm := Nat.lt_or_ge m n
      ·
        exfalso
        have h1 : (a * φ u * φ ϖ ^ (n - m - 1)) * φ ϖ * φ ϖ ^ m = φ v * φ ϖ ^ m := by
          have : n = (n - m - 1) + 1 + m := by
            omega
          rw [this] at hrs
          simp only [map_mul, map_pow, pow_add, pow_one] at hrs
          simpa only [mul_assoc] using hrs
        have h2 : (a * φ u * φ ϖ ^ (n - m - 1)) * φ ϖ = φ v := mul_right_cancel₀ (pow_ne_zero m hϖA) h1
        apply hϖ.not_isUnit ((isUnit_map_iff φ ϖ).mp _)
        have hv : IsUnit (φ v) := (Units.isUnit v).map φ
        rw [← h2] at hv
        apply isUnit_of_mul_isUnit_right hv
      ·
        refine ⟨((u⁻¹ : Rˣ) : R) * v * ϖ ^ (m - n), ?_⟩
        have h1 : a * φ u * φ ϖ ^ n = φ v * φ ϖ ^ (m - n) * φ ϖ ^ n := by
          rw [mul_assoc (φ v), ← pow_add, Nat.sub_add_cancel hnm]
          simpa only [map_mul, map_pow, mul_assoc] using hrs
        have h2 : a * φ u = φ v * φ ϖ ^ (m - n) := mul_right_cancel₀ (pow_ne_zero n hϖA) h1
        have hu : φ ((u⁻¹ : Rˣ) : R) * φ u = 1 := by
          rw [← map_mul, Units.inv_mul, map_one]
        calc
          _ = φ ((u⁻¹ : Rˣ) : R) * (φ v * φ ϖ ^ (m - n)) := by
            rw [map_mul, map_mul, map_pow, mul_assoc]
          _ = φ ((u⁻¹ : Rˣ) : R) * (a * φ u) := by
            rw [h2]
          _ = a * (φ ((u⁻¹ : Rˣ) : R) * φ u) := by
            ring
          _ = a := by
            rw [hu, mul_one]
  refine (ConcreteCategory.isIso_iff_bijective (π.stalkMap γ)).mpr ⟨hinj, hsurj⟩

/--
[AlgebraicGeometry_Scheme_Hom_isIso_stalkMap_of_isIso_stalkMap_genericPoint](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_isIso_stalkMap_of_isIso_stalkMap_genericPoint.lean)
-/
@[path]
private lemma main
  {Γ G : (Scheme : Type (u + 1))} [IsIntegral Γ] [IsIntegral G]
  (π : Γ ⟶ G)
  (γ : Γ) [IsDiscreteValuationRing (G.presheaf.stalk (π.base γ))]
  -- given
  (hgen : π.base (genericPoint Γ) = genericPoint G)
  (hbir : IsIso (π.stalkMap (genericPoint Γ)))
  (_ : γ ≠ genericPoint Γ) :
  -- imply
  IsIso (π.stalkMap γ) := by
  -- proof
  apply stalkMap_dvr π γ hgen hbir


-- created on 2026-10-20
