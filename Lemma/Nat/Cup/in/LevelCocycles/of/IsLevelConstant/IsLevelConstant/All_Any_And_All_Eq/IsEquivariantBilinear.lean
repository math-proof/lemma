import Mathlib
import sympy.Basic
import Lemma.GroupCohomology.ContinuousH2
import Lemma.GroupCohomology.CupProduct
open CategoryTheory groupCohomology


/-- ported from external source -/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G]
  {r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  {A B N : Rep.{u} k G}
  {φ : A →ₗ[k] B →ₗ[k] N}
  {f : cocycles₁ A}
  {g : cocycles₁ B}
-- given
  (hφ : Rep.IsEquivariantBilinear A B N φ)
  (hB : ∀ b : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ s, r s ∈ F.fixingSubgroup → B.ρ s b = b)
  (hf : IsLevelConstant₁ r (⇑f))
  (hg : IsLevelConstant₁ r (⇑g)) :
-- imply
  (cup φ hφ f g : G × G → N) ∈ levelCocycles₂ r N := by
  classical
    refine (mem_levelCocycles₂_iff r N _).2 ⟨(cup φ hφ f g).2, ?_⟩
    obtain ⟨Ff, hFf, hf'⟩ := hf
    obtain ⟨Fg, hFg, hg'⟩ := hg
    have := hFf; have := hFg
    have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
    have : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
    have : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
    let U : Subgroup G := Fg.fixingSubgroup.comap r
    have : Fg.fixingSubgroup.FiniteIndex := by
-- proof
      refine ⟨?_⟩
      rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
      apply Module.finrank_pos.ne'
    have : Finite ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ Fg.fixingSubgroup) :=
      Subgroup.finite_quotient_of_finiteIndex
    let ψ : G ⧸ U → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ Fg.fixingSubgroup :=
      Quotient.map' r fun a b hab => by
        rw [QuotientGroup.leftRel_apply] at hab ⊢
        show (r a)⁻¹ * r b ∈ Fg.fixingSubgroup
        rwa [← map_inv, ← map_mul]
    have hψ : Function.Injective ψ := by
      intro x y hxy
      induction x using QuotientGroup.induction_on with
      | H a =>
        induction y using QuotientGroup.induction_on with
        | H b =>
          have h : (QuotientGroup.mk (r a) : _ ⧸ Fg.fixingSubgroup) = QuotientGroup.mk (r b) := hxy
          rw [QuotientGroup.eq, ← map_inv, ← map_mul] at h
          refine QuotientGroup.eq.2 h
    have : Finite (G ⧸ U) := Finite.of_injective ψ hψ
    choose Fv hFv hfix using fun c : G ⧸ U => hB (g c.out)
    have := hFv
    refine ⟨Ff ⊔ Fg ⊔ ⨆ c, Fv c, inferInstance, fun s t u u' hu hu' => ?_⟩
    have huf : r u ∈ Ff.fixingSubgroup := IntermediateField.fixingSubgroup_antitone (le_sup_left.trans le_sup_left) hu
    have hu'g : r u' ∈ Fg.fixingSubgroup := IntermediateField.fixingSubgroup_antitone (le_sup_right.trans le_sup_left) hu'
    have huv : ∀ c, r u ∈ (Fv c).fixingSubgroup := fun c =>
      IntermediateField.fixingSubgroup_antitone ((le_iSup Fv c).trans le_sup_right) hu
    have hgt : g t = g ((t : G ⧸ U).out) := by
      obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul U t
      rw [hv, hg' t v v.2]
    rw [cup_apply, cup_apply, hf' s u huf, hg' t u' hu'g, map_mul, Module.End.mul_apply, hgt, hfix _ u (huv _)]


-- created on 2026-10-23
