module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion.booleanFourier.sum_chi
open Finset BigOperators BooleanFourier Bool


public section

/--
[sum_chi_mul_chi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {x y : Fin n → Bool} :
-- imply
  ∑ S : Finset (Fin n), chi S x * chi S y = if x = y then (2 : ℝ) ^ n else 0 := by
-- proof
  classical
  have hprod : ∀ S : Finset (Fin n),
    chi S x * chi S y = ∏ i ∈ S, (boolToReal (x i) * boolToReal (y i)) := by
    intro S
    simp only [chi, Finset.prod_mul_distrib]
  simp_rw [hprod]
  have hkey : ∑ S : Finset (Fin n),
    ∏ i ∈ S, (boolToReal (x i) * boolToReal (y i)) =
    ∏ i : Fin n, (1 + boolToReal (x i) * boolToReal (y i)) := by
    conv_lhs =>
      rw [show (∑ S : Finset (Fin n),
        ∏ i ∈ S, (boolToReal (x i) * boolToReal (y i))) =
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∏ i ∈ S, (boolToReal (x i) * boolToReal (y i)) by
          rw [Finset.powerset_univ]]
    rw [← Finset.prod_one_add]
  rw [hkey]
  simp_rw [one_add_boolToReal_mul_boolToReal]
  split_ifs with h
  ·
    subst h
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ·
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)


theorem BooleanFourier.sum_chi_mul_chi
  {n : ℕ}
  {x y : Fin n → Bool} :
-- imply
  ∑ S : Finset (Fin n), chi S x * chi S y = if x = y then (2 : ℝ) ^ n else 0 := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
