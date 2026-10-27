import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial Module
open scoped DirectSum


/--
[Polynomial_finrank_torsionBy_X_pow_sub_one_eq_sum_finrank_torsionBy_cyclotomic](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_finrank_torsionBy_X_pow_sub_one_eq_sum_finrank_torsionBy_cyclotomic.lean)
-/
@[path]
private lemma main
  {M : Type u} [AddCommGroup M] [Module ℚ[X] M] [Module ℚ M] [IsScalarTower ℚ ℚ[X] M] [FiniteDimensional ℚ M]
  {e : ℕ}
-- given
  (he : 0 < e) :
-- imply
  Module.finrank ℚ (Submodule.torsionBy ℚ[X] M ((X : ℚ[X]) ^ e - 1)) =
      ∑ d ∈ e.divisors, Module.finrank ℚ (Submodule.torsionBy ℚ[X] M (cyclotomic d ℚ)) := by
-- proof
  classical
    have hprod : ∏ d ∈ e.divisors, cyclotomic d ℚ = (X : ℚ[X]) ^ e - 1 := prod_cyclotomic_eq_X_pow_sub_one he ℚ
    have hcop : (e.divisors : Set ℕ).Pairwise (Function.onFun IsCoprime fun d => cyclotomic d ℚ) :=
      fun i _ j _ hij => cyclotomic.isCoprime_rat hij
    have hTtors : Module.IsTorsionBy ℚ[X] (Submodule.torsionBy ℚ[X] M ((X : ℚ[X]) ^ e - 1)) (∏ d ∈ e.divisors, cyclotomic d ℚ) := by
      intro x
      rw [hprod]
      exact Subtype.ext x.2
    have hint := Submodule.torsionBy_isInternal hcop hTtors
    have hTfin : Module.Finite ℚ (Submodule.torsionBy ℚ[X] M ((X : ℚ[X]) ^ e - 1)) :=
      Module.Finite.of_injective ((Submodule.torsionBy ℚ[X] M ((X : ℚ[X]) ^ e - 1)).subtype.restrictScalars ℚ) Subtype.val_injective
    have : ∀ d : e.divisors, Module.Finite ℚ
      (Submodule.torsionBy ℚ[X] (Submodule.torsionBy ℚ[X] M ((X : ℚ[X]) ^ e - 1)) (cyclotomic d ℚ)) := fun d =>
      Module.Finite.of_injective ((Submodule.torsionBy ℚ[X] (Submodule.torsionBy ℚ[X] M ((X : ℚ[X]) ^ e - 1))
        (cyclotomic d ℚ)).subtype.restrictScalars ℚ) Subtype.val_injective
    have : ∀ d : e.divisors, Module.Free ℚ
      (Submodule.torsionBy ℚ[X] (Submodule.torsionBy ℚ[X] M ((X : ℚ[X]) ^ e - 1)) (cyclotomic d ℚ)) := fun d =>
      Module.Free.of_divisionRing ℚ (Submodule.torsionBy ℚ[X] (Submodule.torsionBy ℚ[X] M ((X : ℚ[X]) ^ e - 1)) (cyclotomic d ℚ))
    let eqv := (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun d : e.divisors =>
        Submodule.torsionBy ℚ[X] (Submodule.torsionBy ℚ[X] M ((X : ℚ[X]) ^ e - 1)) (cyclotomic d ℚ)) hint).symm
    have hfr := (eqv.restrictScalars ℚ).finrank_eq
    rw [Module.finrank_directSum] at hfr
    rw [hfr, ← Finset.sum_coe_sort e.divisors]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hle : Submodule.torsionBy ℚ[X] M (cyclotomic d ℚ) ≤ Submodule.torsionBy ℚ[X] M ((X : ℚ[X]) ^ e - 1) := by
      intro x hx
      rw [Submodule.mem_torsionBy_iff] at hx ⊢
      obtain ⟨c, hc⟩ : cyclotomic (d : ℕ) ℚ ∣ (X : ℚ[X]) ^ e - 1 := by
        rw [← hprod]; exact Finset.dvd_prod_of_mem _ d.2
      rw [hc, mul_comm, mul_smul, hx, smul_zero]
    have heq : Submodule.torsionBy ℚ[X] (Submodule.torsionBy ℚ[X] M ((X : ℚ[X]) ^ e - 1)) (cyclotomic d ℚ) =
        (Submodule.torsionBy ℚ[X] M (cyclotomic d ℚ)).comap (Submodule.torsionBy ℚ[X] M ((X : ℚ[X]) ^ e - 1)).subtype := by
      ext x
      simp only [Submodule.mem_torsionBy_iff, Submodule.mem_comap, Submodule.subtype_apply]
      constructor
      ·
        intro h; have := congrArg Subtype.val h; simpa using this
      ·
        intro h; exact Subtype.ext (by simpa using h)
    rw [heq]
    exact ((Submodule.comapSubtypeEquivOfLe hle).restrictScalars ℚ).finrank_eq


-- created on 2026-10-23
