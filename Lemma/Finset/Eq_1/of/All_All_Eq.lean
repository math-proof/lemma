import Mathlib
import sympy.Basic


/--
[KummerTheory_algEquiv_eq_one_of_forall_apply_eq_of_isSplittingField](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_KummerTheory_algEquiv_eq_one_of_forall_apply_eq_of_isSplittingField.lean)
-/
@[path]
private lemma main
  {K L : Type*} [Field K] [Field L] [Algebra K L]
  {n : ℕ}
  {S : Finset Kˣ} [Polynomial.IsSplittingField K L (∏ u ∈ S, (Polynomial.X ^ n - Polynomial.C ((u : Kˣ) : K)))]
-- given
  (σ : L ≃ₐ[K] L)
  (hσ : ∀ α : L, ∀ u ∈ S, α ^ n = algebraMap K L (u : K) → σ α = α) :
-- imply
  σ = 1 := by
-- proof
  classical
  set f : Polynomial K := ∏ u ∈ S, (Polynomial.X ^ n - Polynomial.C ((u : Kˣ) : K)) with hf
  have hadj := Polynomial.IsSplittingField.adjoin_rootSet L f
  have key : (σ : L →ₐ[K] L) = AlgHom.id K L := by
    apply AlgHom.ext_of_adjoin_eq_top hadj
    intro α hα
    rw [Polynomial.mem_rootSet] at hα
    obtain ⟨-, hα⟩ := hα
    rw [hf, map_prod, Finset.prod_eq_zero_iff] at hα
    obtain ⟨u, hu, hαu⟩ := hα
    have hαn : α ^ n = algebraMap K L (u : K) := by
      rw [← sub_eq_zero]
      simpa using hαu
    change σ α = α
    exact hσ α u hu hαn
  ext x
  exact DFunLike.congr_fun key x


-- created on 2026-10-05
