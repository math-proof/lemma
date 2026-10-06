import Mathlib
import sympy.Basic

open IntermediateField

/--
[IntermediateField_norm_algebraNorm_eq_pow_finrank_padic](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IntermediateField_norm_algebraNorm_eq_pow_finrank_padic.lean)
-/
@[main]
private lemma main
  {q : ℕ} [Fact q.Prime]
  {K : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] K]
  {L : IntermediateField K (PadicAlgCl q)} [FiniteDimensional K L]
  {w : L} :
-- imply
  ‖((Algebra.norm K w : K) : PadicAlgCl q)‖ = ‖(w : PadicAlgCl q)‖ ^ Module.finrank K L := by
-- proof
  classical

  have key : ∀ y : PadicAlgCl q, ‖y‖ = spectralValue (minpoly ℚ_[q] y) := fun y => by
    rw [← PadicAlgCl.spectralNorm_eq]; rfl
  have hemb : ∀ σ : L →ₐ[K] PadicAlgCl q, ‖σ w‖ = ‖(w : PadicAlgCl q)‖ := fun σ => by
    rw [key, key]
    congr 1
    have h1 : minpoly ℚ_[q] (σ w) = minpoly ℚ_[q] w :=
      minpoly.algHom_eq (σ.restrictScalars ℚ_[q]) (σ.restrictScalars ℚ_[q]).injective w
    have h2 : minpoly ℚ_[q] ((w : PadicAlgCl q)) = minpoly ℚ_[q] w :=
      minpoly.algHom_eq ((L.val).restrictScalars ℚ_[q]) ((L.val).restrictScalars ℚ_[q]).injective w
    rw [h1, h2]
  have hprod := Algebra.norm_eq_prod_embeddings K (PadicAlgCl q) w
  change ((Algebra.norm K w : K) : PadicAlgCl q) = _ at hprod
  rw [hprod, norm_prod, Finset.prod_congr rfl (fun σ _ => hemb σ), Finset.prod_const, Finset.card_univ,
    AlgHom.card]


-- created on 2026-10-05
