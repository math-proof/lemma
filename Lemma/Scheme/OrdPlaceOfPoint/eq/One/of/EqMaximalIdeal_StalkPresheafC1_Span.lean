import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_CurveModel
import Lemma.Int.P2MUtil

open CategoryTheory AlgebraicGeometry IsLocalRing


/--
[AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span.lean)
-/
@[path]
private lemma main
  {K : Type u} [Field K]
  {L : Type v} [Field L] [Algebra K L]
  {M : AlgebraicCurve.CurveModel K L}
  {x : closedPoints M.C}
  {g : M.C.presheaf.stalk x.1}
-- given
  (hg : IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) = Ideal.span {g}) :
-- imply
  (M.placeOfPoint x).ord (M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField g)) = 1 := by
  set V := (M.placeOfPoint x).toValuationSubring with hV
  set θ : M.C.presheaf.stalk x.1 →+* L :=
    (M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField) with hθ_def
  have hθ : ∀ s, θ s = M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField s) := fun s => rfl
  have hθ_inj : Function.Injective θ :=
    M.ffEquiv.symm.injective.comp (IsFractionRing.injective (M.C.presheaf.stalk x.1) M.C.functionField)
  have hrange : θ.range = V.toSubring := M.range_stalk_eq x
  have hmemV : ∀ s, θ s ∈ V := fun s => by
    have : θ s ∈ θ.range := ⟨s, rfl⟩
    rwa [hrange] at this
  set ψ : M.C.presheaf.stalk x.1 →+* V := θ.codRestrict V hmemV with hψ_def
  have hψ : ∀ s, ((ψ s : V) : L) = θ s := fun s => rfl
  have hψ_bij : Function.Bijective ψ := by
-- proof
    refine ⟨fun a b hab => hθ_inj (by rw [← hψ, ← hψ, hab]), fun y => ?_⟩
    have hy : (y : L) ∈ θ.range := by rw [hrange]; exact y.2
    obtain ⟨s, hs⟩ := hy
    exact ⟨s, Subtype.ext (by rw [hψ, hs])⟩
  set ε : M.C.presheaf.stalk x.1 ≃+* V := RingEquiv.ofBijective ψ hψ_bij with hε_def
  have hε : ∀ s, ((ε s : V) : L) = θ s := fun s => rfl
  have hmax : IsLocalRing.maximalIdeal V = Ideal.span {ε g} := by
    have h1 : Ideal.map ε (IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1)) = IsLocalRing.maximalIdeal V := by
      have hM : (Ideal.map ε (IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1))).IsMaximal :=
        Ideal.map_isMaximal_of_equiv ε
      refine IsLocalRing.eq_maximalIdeal hM
    rw [← h1, hg, Ideal.map_span, Set.image_singleton]
  have hg0 : (ε g : V) ≠ 0 := by
    intro h0
    have hbot : IsLocalRing.maximalIdeal V = ⊥ := by rw [hmax, h0, Ideal.span_singleton_eq_bot]
    refine IsDiscreteValuationRing.not_a_field V hbot
  have hirr : Irreducible (ε g : V) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (ε g) hg0 hmax
  rw [← hθ, ← hε]
  exact (M.placeOfPoint x).ord_coe_irreducible hirr


-- created on 2026-10-23
-- updated on 2026-10-24
