import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[roth_triangular_sum_lower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {θ δ : ℝ}
  {r k : ℕ}
-- given
  (hθ : 0 < θ)
  (hθone : θ ≤ 1)
  (hδ : δ ≤ θ / 4)
  (hr : 0 < r)
  (hrlarge : 16 ≤ θ * r)
  (hk : 0 < k)
  (hkr : k ≤ r + 1) :
-- imply
  θ ^ 2 / 64 ≤
    (∑ t : Fin k, max 0 (θ - δ - (t : ℝ) / r)) / k := by
-- proof
  let N : ℕ := ⌊θ * r / 8⌋₊
  have hxnonneg : 0 ≤ θ * (r : ℝ) / 8 := by positivity
  have hxlarge : 2 ≤ θ * (r : ℝ) / 8 := by linarith
  have hNle : (N : ℝ) ≤ θ * r / 8 := Nat.floor_le hxnonneg
  have hxlt : θ * r / 8 < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hNlower : θ * (r : ℝ) / 16 ≤ N := by linarith
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hNlower
    exact_mod_cast this
  have hterm : ∀ t : Fin k, t.val < N →
      θ / 2 ≤ max 0 (θ - δ - (t : ℝ) / r) := by
    intro t ht
    have htN : (t.val : ℝ) < N := by exact_mod_cast ht
    have htx : (t.val : ℝ) < θ * r / 8 := htN.trans_le hNle
    have htdiv : (t.val : ℝ) / r < θ / 8 := by
      apply (div_lt_iff₀ (by exact_mod_cast hr : (0 : ℝ) < r)).2
      nlinarith
    exact (by linarith : θ / 2 ≤ θ - δ - (t : ℝ) / r).trans (le_max_right _ _)
  apply (le_div_iff₀ (by exact_mod_cast hk : (0 : ℝ) < k)).2
  if hkN : k ≤ N then
    have hsum : (k : ℝ) * (θ / 2) ≤
        ∑ t : Fin k, max 0 (θ - δ - (t : ℝ) / r) := calc
        _ = ∑ _ : Fin k, θ / 2 := by simp
        _ ≤ ∑ t : Fin k, max 0 (θ - δ - (t : ℝ) / r) := by
          gcongr with t
          exact hterm t (lt_of_lt_of_le t.isLt hkN)
    calc
      _ ≤ (k : ℝ) * (θ / 2) := by
        have : θ ^ 2 / 64 ≤ θ / 2 := by nlinarith [sq_nonneg θ]
        nlinarith
      _ ≤ _ := hsum
  else
    have hNk : N ≤ k := Nat.le_of_lt (lt_of_not_ge hkN)
    let S : Finset (Fin k) := Finset.univ.filter fun t ↦ t.val < N
    have hcardS : S.card = N := by
      rw [← Fintype.card_coe]
      let e : S ≃ Fin N :=
        { toFun := fun t ↦ ⟨t.val.val, by
            have := t.property
            change t.val ∈ Finset.univ.filter (fun u : Fin k ↦ u.val < N) at this
            exact (Finset.mem_filter.mp this).2⟩
          invFun := fun t ↦ ⟨⟨t.val, t.isLt.trans_le hNk⟩, by simp [S]⟩
          left_inv := by intro t; ext; rfl
          right_inv := by intro t; ext; rfl }
      exact (Fintype.card_congr e).trans (Fintype.card_fin N)
    have hsumS : (N : ℝ) * (θ / 2) ≤
        ∑ t ∈ S, max 0 (θ - δ - (t : ℝ) / r) := calc
        _ = ∑ _ ∈ S, θ / 2 := by simp [hcardS]
        _ ≤ ∑ t ∈ S, max 0 (θ - δ - (t : ℝ) / r) := by
          gcongr with t ht
          exact hterm t (by simpa [S] using ht)
    have hsumAll : (N : ℝ) * (θ / 2) ≤
        ∑ t : Fin k, max 0 (θ - δ - (t : ℝ) / r) :=
      hsumS.trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ ↦ le_max_left _ _))
    have hkrR : (k : ℝ) ≤ 2 * r := by
      exact_mod_cast (hkr.trans (by omega : r + 1 ≤ 2 * r))
    calc
      _ ≤ θ ^ 2 * r / 32 := by nlinarith [sq_nonneg θ]
      _ ≤ (N : ℝ) * (θ / 2) := by nlinarith
      _ ≤ _ := hsumAll


-- created on 2026-10-21
