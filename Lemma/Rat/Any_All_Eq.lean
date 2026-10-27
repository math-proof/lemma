import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[AlgebraicClosure_exists_ratAlgEquiv_of_padicAlgEquiv_comp](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicClosure_exists_ratAlgEquiv_of_padicAlgEquiv_comp.lean)
-/
@[path]
private lemma main
  {p : ℕ} [Fact p.Prime]
  {ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]}
  {σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]} :
-- imply
  ∃ σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    ∀ x : AlgebraicClosure ℚ, σ (ι x) = ι (σ' x) := by
-- proof
  have hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    (AlgebraicClosure.instIsAlgClosure ℚ).isAlgebraic
  let σι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p] :=
    (σ.restrictScalars ℚ).toAlgHom.comp ι
  let ιR : AlgebraicClosure ℚ ≃ₐ[ℚ] ι.fieldRange := AlgEquiv.ofInjectiveField ι
  have hAC : IsAlgClosed ι.fieldRange := by
    have : IsAlgClosed (AlgebraicClosure ℚ) := inferInstance
    apply IsAlgClosed.of_ringEquiv (AlgebraicClosure ℚ) ι.fieldRange ιR.toRingEquiv
  have hmem : ∀ x, σι x ∈ ι.fieldRange := by
    intro x
    have hint : IsIntegral (ι.fieldRange) (σι x) :=
      (((hAlg.isAlgebraic x).isIntegral).map σι).tower_top
    have hdeg : (minpoly (ι.fieldRange) (σι x)).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible hint)
    obtain ⟨w, hw⟩ := minpoly.mem_range_of_degree_eq_one _ (σι x) hdeg
    exact hw ▸ w.property
  let σιR : AlgebraicClosure ℚ →ₐ[ℚ] ι.fieldRange :=
    { toFun := fun x => ⟨σι x, hmem x⟩, map_one' := Subtype.ext σι.map_one, map_mul' := fun a b => Subtype.ext (σι.map_mul a b), map_zero' := Subtype.ext σι.map_zero, map_add' := fun a b => Subtype.ext (σι.map_add a b), commutes' := fun r => Subtype.ext (σι.commutes r) }
  let σ'hom : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ :=
    ιR.symm.toAlgHom.comp σιR
  have hbij : Function.Bijective σ'hom :=
    Algebra.IsAlgebraic.algHom_bijective σ'hom
  refine ⟨AlgEquiv.ofBijective σ'hom hbij, fun x => ?_⟩
  show σ (ι x) = ι (σ'hom x)
  have h2 : ∀ y, (ιR y : AlgebraicClosure ℚ_[p]) = ι y := fun y => rfl
  calc
    _ = σι x := rfl
    _ = ((σιR x : ι.fieldRange) : AlgebraicClosure ℚ_[p]) := rfl
    _ = ((ιR (ιR.symm (σιR x)) : ι.fieldRange) : AlgebraicClosure ℚ_[p]) := by
      rw [ιR.apply_symm_apply]
    _ = ι (ιR.symm (σιR x)) := h2 _
    _ = ι (σ'hom x) := rfl


-- created on 2026-10-13
