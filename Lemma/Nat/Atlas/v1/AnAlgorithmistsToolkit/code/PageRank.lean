import Mathlib
import sympy.Basic
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.PageRank
open Matrix Finset PageRank
open scoped Matrix BigOperators


namespace PageRank

/--
[pageRankVec_fixed_point](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma pageRankVec_fixed_point
  {n : ℕ}
  {α : ℝ}
  {W : Matrix (Fin n) (Fin n) ℝ}
  {s : Fin n → ℝ}
-- given
  (hW : IsUnit ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W)) :
-- imply
  pageRankVec α W s = α • s + (1 - α) • (W *ᵥ (pageRankVec α W s)) := by
-- proof
  set M := (1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W with hM_def
  set x := pageRankVec α W s
  suffices h : x - (1 - α) • (W *ᵥ x) = α • s from
    eq_add_of_sub_eq h
  have hMx : M *ᵥ x = α • s := by
    show M *ᵥ (M⁻¹ *ᵥ (α • s)) = α • s
    rw [mulVec_mulVec, mul_nonsing_inv _ (hW.map Matrix.detMonoidHom), one_mulVec]
  rw [← hMx]
  simp only [M, sub_mulVec, one_mulVec, smul_mulVec]

end PageRank

namespace PageRank

/--
[pageRankVec_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma pageRankVec_unique
  {n : ℕ}
  {α : ℝ}
  {W : Matrix (Fin n) (Fin n) ℝ}
  {s : Fin n → ℝ}
  {x : Fin n → ℝ}
-- given
  (hW : IsUnit ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W))
  (hx : x = α • s + (1 - α) • (W *ᵥ x)) :
-- imply
  x = pageRankVec α W s := by
-- proof
  set M := (1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W with hM_def
  have hMx : M *ᵥ x = α • s := by
    have hM_expand : M *ᵥ x = x - (1 - α) • (W *ᵥ x) := by
      simp only [M, sub_mulVec, one_mulVec, smul_mulVec]
    rw [hM_expand]
    have hsub : x - (1 - α) • (W *ᵥ x) = α • s := sub_eq_of_eq_add hx
    exact hsub
  show x = M⁻¹ *ᵥ (α • s)
  calc x = (M⁻¹ * M) *ᵥ x := by
    rw [nonsing_inv_mul _ (hW.map Matrix.detMonoidHom), one_mulVec]
    _ = M⁻¹ *ᵥ (M *ᵥ x) := by rw [mulVec_mulVec]
    _ = M⁻¹ *ᵥ (α • s) := by rw [hMx]

end PageRank

namespace PageRank

/--
[pageRankVec_comm_W](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma pageRankVec_comm_W
  {n : ℕ}
  {α : ℝ}
  {W : Matrix (Fin n) (Fin n) ℝ}
  {s : Fin n → ℝ}
-- given
  (hcomm : Commute W ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W)⁻¹) :
-- imply
  pageRankVec α W (W *ᵥ s) = W *ᵥ (pageRankVec α W s) := by
-- proof
  set M_inv := ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W)⁻¹
  show M_inv *ᵥ (α • (W *ᵥ s)) = W *ᵥ (M_inv *ᵥ (α • s))
  simp_rw [Matrix.mulVec_smul]
  congr 1
  rw [mulVec_mulVec, mulVec_mulVec, hcomm.eq]

end PageRank

namespace PageRank

/--
[pageRankVec_comm_W_of_isUnit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma pageRankVec_comm_W_of_isUnit
  {n : ℕ}
  {α : ℝ}
  {W : Matrix (Fin n) (Fin n) ℝ}
  {s : Fin n → ℝ}
-- given
  (hW : IsUnit ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W)) :
-- imply
  pageRankVec α W (W *ᵥ s) = W *ᵥ (pageRankVec α W s) := by
-- proof
  set x' := W *ᵥ (pageRankVec α W s)
  have hfp : x' = α • (W *ᵥ s) + (1 - α) • (W *ᵥ x') := by
    show W *ᵥ (pageRankVec α W s) = α • (W *ᵥ s) + (1 - α) • (W *ᵥ (W *ᵥ (pageRankVec α W s)))
    have key : α • (W *ᵥ s) + (1 - α) • (W *ᵥ (W *ᵥ (pageRankVec α W s)))
      = W *ᵥ (α • s + (1 - α) • (W *ᵥ (pageRankVec α W s))) := by
      simp only [mulVec_add, Matrix.mulVec_smul, mulVec_mulVec]
    rw [key, ← pageRankVec_fixed_point α W s hW]
  exact (pageRankVec_unique α W (W *ᵥ s) hW x' hfp).symm

end PageRank

namespace PageRank

/--
[pageRankVec_eq2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma pageRankVec_eq2
  {n : ℕ}
  {α : ℝ}
  {W : Matrix (Fin n) (Fin n) ℝ}
  {s : Fin n → ℝ}
-- given
  (hW : IsUnit ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W))
  (hcomm : Commute W ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W)⁻¹) :
-- imply
  pageRankVec α W s = α • s + (1 - α) • pageRankVec α W (W *ᵥ s) := by
-- proof
  rw [pageRankVec_comm_W α W s hcomm]
  exact pageRankVec_fixed_point α W s hW

end PageRank

namespace PageRank

/--
[pageRankVec_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma pageRankVec_add
  {n : ℕ}
  {α : ℝ}
  {W : Matrix (Fin n) (Fin n) ℝ}
  {s₁ s₂ : Fin n → ℝ} :
-- imply
  pageRankVec α W (s₁ + s₂) = pageRankVec α W s₁ + pageRankVec α W s₂ := by
-- proof
  unfold pageRankVec
  rw [smul_add, mulVec_add]

end PageRank

namespace PageRank

/--
[pageRankVec_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma pageRankVec_smul
  {n : ℕ}
  {α : ℝ}
  {W : Matrix (Fin n) (Fin n) ℝ}
  {c : ℝ}
  {s : Fin n → ℝ} :
-- imply
  pageRankVec α W (c • s) = c • pageRankVec α W s := by
-- proof
  show ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W)⁻¹ *ᵥ (α • (c • s)) =
    c • (((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W)⁻¹ *ᵥ (α • s))
  rw [show α • (c • s) = c • (α • s) from smul_comm α c s, mulVec_smul]

end PageRank

namespace PageRank

/--
[pageRankVec_linear](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma pageRankVec_linear
  {n : ℕ}
  {α : ℝ}
  {W : Matrix (Fin n) (Fin n) ℝ}
  {c d : ℝ}
  {v w : Fin n → ℝ} :
-- imply
  pageRankVec α W (c • v + d • w) = c • pageRankVec α W v + d • pageRankVec α W w := by
-- proof
  rw [pageRankVec_add, pageRankVec_smul, pageRankVec_smul]

end PageRank

namespace PageRank

/--
[pageRankVec_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma pageRankVec_sub
  {n : ℕ}
  {α : ℝ}
  {W : Matrix (Fin n) (Fin n) ℝ}
  {s₁ s₂ : Fin n → ℝ} :
-- imply
  pageRankVec α W (s₁ - s₂) = pageRankVec α W s₁ - pageRankVec α W s₂ := by
-- proof
  unfold pageRankVec
  rw [smul_sub, mulVec_sub]

end PageRank

namespace PageRank

/--
[pageRankVec_invariant_preserved](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma pageRankVec_invariant_preserved
  {n : ℕ}
  {α : ℝ}
  {W : Matrix (Fin n) (Fin n) ℝ}
  {s p r : Fin n → ℝ}
  {u : Fin n}
-- given
  (hW : IsUnit ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W))
  (hcomm : Commute W ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 - α) • W)⁻¹)
  (hinv : p = pageRankVec α W (s - r)) :
-- imply
  let χ_u : Fin n → ℝ := Pi.single u 1 let p' := p + (α * r u) • χ_u let r' := r - r u • χ_u + ((1 - α) * r u) • (W *ᵥ χ_u) p' = pageRankVec α W (s - r') := by
-- proof
  intro χ_u p' r'
  have hinv_sum : p + pageRankVec α W r = pageRankVec α W s := by
    rw [hinv, pageRankVec_sub, sub_add_cancel]
  have hkey : pageRankVec α W r = (α * r u) • χ_u + pageRankVec α W r' := by
    have hr_split : r = (r - r u • χ_u) + r u • χ_u := by
      ext i; simp [sub_add_cancel]
    have h1 : pageRankVec α W r =
      pageRankVec α W (r - r u • χ_u) + pageRankVec α W (r u • χ_u) := by
      conv_lhs => rw [hr_split]
      exact pageRankVec_add α W _ _
    have h2 : pageRankVec α W (r u • χ_u) = r u • pageRankVec α W χ_u := by
      exact pageRankVec_smul α W (r u) χ_u
    have h3 : pageRankVec α W χ_u = α • χ_u + (1 - α) • pageRankVec α W (W *ᵥ χ_u) := by
      exact pageRankVec_eq2 α W χ_u hW hcomm
    rw [h2, h3] at h1
    have h4 : r u • (α • χ_u + (1 - α) • pageRankVec α W (W *ᵥ χ_u)) =
      (α * r u) • χ_u + ((1 - α) * r u) • pageRankVec α W (W *ᵥ χ_u) := by
      rw [smul_add, smul_comm (r u) α, smul_smul, smul_comm (r u) (1 - α), smul_smul]
    rw [h4] at h1
    have h5 : ((1 - α) * r u) • pageRankVec α W (W *ᵥ χ_u) =
      pageRankVec α W (((1 - α) * r u) • (W *ᵥ χ_u)) := by
      exact (pageRankVec_smul α W ((1 - α) * r u) (W *ᵥ χ_u)).symm
    rw [h5] at h1
    have h6 : pageRankVec α W (r - r u • χ_u) + pageRankVec α W (((1 - α) * r u) • (W *ᵥ χ_u)) =
      pageRankVec α W r' := by
      rw [← pageRankVec_add]
    rw [show pageRankVec α W (r - r u • χ_u) + ((α * r u) • χ_u + pageRankVec α W (((1 - α) * r u) • (W *ᵥ χ_u)))
      = (α * r u) • χ_u + (pageRankVec α W (r - r u • χ_u) + pageRankVec α W (((1 - α) * r u) • (W *ᵥ χ_u)))
      from by abel] at h1
    rwa [h6] at h1
  have hgoal : p' + pageRankVec α W r' = pageRankVec α W s := by
    rw [show p' = p + (α * r u) • χ_u from rfl]
    rw [show p + (α * r u) • χ_u + pageRankVec α W r' =
      p + ((α * r u) • χ_u + pageRankVec α W r') from add_assoc _ _ _]
    rwa [← hkey]
  rw [pageRankVec_sub]
  exact eq_sub_of_add_eq hgoal

end PageRank

namespace PageRank

/--
[l1norm_add_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma l1norm_add_le
  {n : ℕ}
  {f g : Fin n → ℝ} :
-- imply
  l1norm (f + g) ≤ l1norm f + l1norm g := by
-- proof
  unfold l1norm
  calc ∑ i, |(f + g) i| ≤ ∑ i, (|f i| + |g i|) :=
    Finset.sum_le_sum (fun i _ => abs_add_le (f i) (g i))
    _ = ∑ i, |f i| + ∑ i, |g i| := Finset.sum_add_distrib

end PageRank

namespace PageRank

/--
[l1norm_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma l1norm_smul
  {n : ℕ}
  {c : ℝ}
  {f : Fin n → ℝ} :
-- imply
  l1norm (c • f) = := by
-- proof
  unfold l1norm
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  rw [Finset.mul_sum]

end PageRank

namespace PageRank

/--
[sum_mul_pi_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma sum_mul_pi_single
  {n : ℕ}
  {W : Matrix (Fin n) (Fin n) ℝ}
  {i u : Fin n} :
-- imply
  ∑ x, W i x * (Pi.single u 1 : Fin n → ℝ) x = W i u := by
-- proof
  rw [Finset.sum_eq_single u]
  · simp [Pi.single_eq_same]
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ u) h

end PageRank

namespace PageRank

/--
[l1norm_sub_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma l1norm_sub_single
  {n : ℕ}
  {r : Fin n → ℝ}
  {u : Fin n}
-- given
  (hr : ∀ i, 0 ≤ r i) :
-- imply
  let χ_u : Fin n → ℝ := Pi.single u 1 l1norm (r - r u • χ_u) = l1norm r - r u := by
-- proof
  intro χ_u
  unfold l1norm
  have key : ∀ i : Fin n, |(r - r u • χ_u) i| = |r i| - (r u • χ_u) i := by
    intro i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, χ_u]
    by_cases hi : i = u
    · subst hi; simp only [Pi.single_eq_same, mul_one]; simp [abs_of_nonneg (hr i)]
    · simp only [Pi.single_eq_of_ne hi, mul_zero, sub_zero]
  simp_rw [key]
  rw [Finset.sum_sub_distrib]
  suffices h : ∑ i : Fin n, (r u • χ_u) i = r u by linarith
  simp only [Pi.smul_apply, smul_eq_mul, χ_u]
  rw [← Finset.mul_sum]
  simp [Finset.sum_pi_single']

end PageRank

namespace PageRank

/--
[l1norm_mulVec_single_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma l1norm_mulVec_single_le
  {n : ℕ}
  {W : Matrix (Fin n) (Fin n) ℝ}
  {u : Fin n}
-- given
  (hW : W ∈ colStochastic ℝ (Fin n)) :
-- imply
  let χ_u : Fin n → ℝ := Pi.single u 1 l1norm (W *ᵥ χ_u) ≤ 1 := by
-- proof
  intro χ_u
  unfold l1norm
  have hWnn : ∀ i j, 0 ≤ W i j := hW.1
  have hWcol : ∀ j, ∑ i, W i j = 1 := (mem_colStochastic_iff_sum.mp hW).2
  have hmul : ∀ i, (W *ᵥ χ_u) i = W i u := by
    intro i; simp only [mulVec, dotProduct, χ_u]; exact sum_mul_pi_single W i u
  conv_lhs => arg 2; ext i; rw [hmul i, abs_of_nonneg (hWnn i u)]
  exact le_of_eq (hWcol u)

end PageRank

namespace PageRank

/--
[residual_decrease_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma residual_decrease_bound
  {n : ℕ}
  {α : ℝ}
  {W : Matrix (Fin n) (Fin n) ℝ}
  {r : Fin n → ℝ}
  {u : Fin n}
-- given
  (hα : 0 < α)
  (hα1 : α < 1)
  (hW : W ∈ colStochastic ℝ (Fin n))
  (hr : ∀ i, 0 ≤ r i) :
-- imply
  let χ_u : Fin n → ℝ := Pi.single u 1 let r' := r - r u • χ_u + ((1 - α) * r u) • (W *ᵥ χ_u) l1norm r' ≤ l1norm r - α * r u := by
-- proof
  intro χ_u r'
  have hα_pos := hα
  have h1α_pos : (0 : ℝ) < 1 - α := by linarith
  have h1 : l1norm r' ≤ l1norm (r - r u • χ_u) + l1norm (((1 - α) * r u) • (W *ᵥ χ_u)) :=
    l1norm_add_le (r - r u • χ_u) (((1 - α) * r u) • (W *ᵥ χ_u))
  have h2 : l1norm (r - r u • χ_u) = l1norm r - r u := l1norm_sub_single r u hr
  have h3 : l1norm (((1 - α) * r u) • (W *ᵥ χ_u)) = (1 - α) * r u * l1norm (W *ᵥ χ_u) := by
    rw [l1norm_smul, abs_of_nonneg (mul_nonneg (le_of_lt h1α_pos) (hr u))]
  have h5 : l1norm (W *ᵥ χ_u) ≤ 1 := l1norm_mulVec_single_le W u hW
  have hle : l1norm (((1 - α) * r u) • (W *ᵥ χ_u)) ≤ (1 - α) * r u := by
    rw [h3]
    have : (1 - α) * r u * l1norm (W *ᵥ χ_u) ≤ (1 - α) * r u * 1 :=
      mul_le_mul_of_nonneg_left h5 (mul_nonneg (le_of_lt h1α_pos) (hr u))
    linarith
  linarith

end PageRank

namespace PageRank

/--
[telescope_decrease](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma telescope_decrease
  {n : ℕ}
  {T : ℕ}
  {a : Fin (T + 1) → ℝ}
  {b : Fin T → ℝ}
-- given
  (h : ∀ i : Fin T, a ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ≤ a ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ - b i) :
-- imply
  a ⟨T, Nat.lt_succ_iff.mpr le_rfl⟩ ≤ a ⟨0, Nat.zero_lt_succ T⟩ - ∑ i : Fin T, b i := by
-- proof
  induction T with
  | zero => simp
  | succ T' ih =>
    have h_last := h ⟨T', Nat.lt_succ_iff.mpr le_rfl⟩
    have ih' := ih (fun i => a ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ _)⟩)
      (fun i => b ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ _)⟩)
      (fun i => by exact h ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ _)⟩)
    have h_sum : ∑ i : Fin (T' + 1), b i =
      (∑ i : Fin T', b ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ _)⟩) +
      b ⟨T', Nat.lt_succ_iff.mpr le_rfl⟩ := by
      rw [Fin.sum_univ_castSucc]; congr 1
    rw [h_sum]
    linarith

end PageRank

namespace PageRank

/--
[pageRank_iteration_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma pageRank_iteration_bound
  {n : ℕ}
  {α ε : ℝ}
  {T : ℕ}
  {d : Fin n → ℝ}
  {residual_norms : Fin (T + 1) → ℝ}
  {vertices : Fin T → Fin n}
  {residual_vals : Fin T → ℝ}
-- given
  (hα : 0 < α)
  (hε : 0 < ε)
  (hd : ∀ v, 1 ≤ d v)
  (h_nonneg : ∀ i, 0 ≤ residual_norms i)
  (h_select : ∀ i : Fin T, ε * d (vertices i) ≤ residual_vals i)
  (h_decrease : ∀ i : Fin T, residual_norms ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ≤ residual_norms ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ - α * residual_vals i) :
-- imply
  (T : ℝ) * (α * ε) ≤ residual_norms ⟨0, Nat.zero_lt_succ T⟩ := by
-- proof
  have h_min_decrease : ∀ i : Fin T,
    residual_norms ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ≤
    residual_norms ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ - α * ε := by
    intro i
    have hεd : ε ≤ residual_vals i :=
      calc ε = ε * 1 := (mul_one ε).symm
        _ ≤ ε * d (vertices i) := by gcongr; exact hd (vertices i)
        _ ≤ residual_vals i := h_select i
    linarith [h_decrease i, mul_le_mul_of_nonneg_left hεd (le_of_lt hα)]
  have h_tel := telescope_decrease residual_norms (fun _ => α * ε) h_min_decrease
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at h_tel
  linarith [h_nonneg ⟨T, Nat.lt_succ_iff.mpr le_rfl⟩]

end PageRank

namespace PageRank

/--
[pageRank_degree_sum_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma pageRank_degree_sum_bound
  {n : ℕ}
  {α ε : ℝ}
  {T : ℕ}
  {d : Fin n → ℝ}
  {residual_norms : Fin (T + 1) → ℝ}
  {vertices : Fin T → Fin n}
  {residual_vals : Fin T → ℝ}
-- given
  (hα : 0 < α)
  (h_nonneg : ∀ i, 0 ≤ residual_norms i)
  (h_select : ∀ i : Fin T, ε * d (vertices i) ≤ residual_vals i)
  (h_decrease : ∀ i : Fin T, residual_norms ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ≤ residual_norms ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ - α * residual_vals i) :
-- imply
  α * ε * ∑ i : Fin T, d (vertices i) ≤ residual_norms ⟨0, Nat.zero_lt_succ T⟩ := by
-- proof
  have h_tel := telescope_decrease residual_norms
    (fun i => α * residual_vals i) h_decrease
  have h_sum_le : α * ε * ∑ i : Fin T, d (vertices i) ≤ ∑ i : Fin T, α * residual_vals i := by
    calc α * ε * ∑ i : Fin T, d (vertices i)
      = ∑ i : Fin T, α * (ε * d (vertices i)) := by rw [Finset.mul_sum]; congr 1; ext i; ring
      _ ≤ ∑ i : Fin T, α * residual_vals i :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h_select i) (le_of_lt hα))
  linarith [h_nonneg ⟨T, Nat.lt_succ_iff.mpr le_rfl⟩]

end PageRank

namespace PageRank

/--
[vol_supp_le_degree_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma vol_supp_le_degree_sum
  {n : ℕ}
  {d : Fin n → ℝ}
  {p : Fin n → ℝ}
  {T : ℕ}
  {vertices : Fin T → Fin n}
-- given
  (hd : ∀ v, 0 ≤ d v)
  (h_supp_covered : ∀ v ∈ vecSupp p, ∃ i : Fin T, vertices i = v) :
-- imply
  vol d (vecSupp p) ≤ ∑ i : Fin T, d (vertices i) := by
-- proof
  classical
  unfold vol
  have h_sub : vecSupp p ⊆ Finset.univ.image vertices := by
    intro v hv
    obtain ⟨i, hi⟩ := h_supp_covered v hv
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  calc ∑ x ∈ vecSupp p, d x
    ≤ ∑ x ∈ Finset.univ.image vertices, d x :=
      Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => hd _)
    _ ≤ ∑ i ∈ Finset.univ, d (vertices i) :=
      Finset.sum_image_le_of_nonneg (fun u _ => hd u)

end PageRank

namespace PageRank

/--
[pageRank_output_quality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma pageRank_output_quality
  {n : ℕ}
  {ε : ℝ}
  {d : Fin n → ℝ}
  {r : Fin n → ℝ}
-- given
  (hd_pos : ∀ v, 0 < d v)
  (h_term : ∀ v : Fin n, r v < ε * d v) :
-- imply
  ∀ v : Fin n, r v / d v < ε := by
-- proof
  intro v
  rw [div_lt_iff₀ (hd_pos v)]
  exact h_term v

end PageRank

namespace PageRank

/--
[pageRank_termination](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PageRank.lean)
-/
@[path]
lemma pageRank_termination
  {n : ℕ}
  {α ε : ℝ}
  {T : ℕ}
  {d : Fin n → ℝ}
  {p : Fin n → ℝ}
  {r_final : Fin n → ℝ}
  {residual_norms : Fin (T + 1) → ℝ}
  {vertices : Fin T → Fin n}
  {residual_vals : Fin T → ℝ}
-- given
  (hα : 0 < α)
  (hε : 0 < ε)
  (hd : ∀ v, 1 ≤ d v)
  (h_init : residual_norms ⟨0, Nat.zero_lt_succ T⟩ = 1)
  (h_nonneg : ∀ i, 0 ≤ residual_norms i)
  (h_select : ∀ i : Fin T, ε * d (vertices i) ≤ residual_vals i)
  (h_decrease : ∀ i : Fin T, residual_norms ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ≤ residual_norms ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ - α * residual_vals i)
  (h_term : ∀ v : Fin n, r_final v < ε * d v)
  (h_supp_covered : ∀ v ∈ vecSupp p, ∃ i : Fin T, vertices i = v) :
-- imply
  (T : ℝ) * (α * ε) ≤ 1 ∧ (∀ v : Fin n, r_final v / d v < ε) ∧ α * ε * vol d (vecSupp p) ≤ 1 := by
-- proof
  have hd_nonneg : ∀ v, 0 ≤ d v := fun v => le_trans (by norm_num : (0 : ℝ) ≤ 1) (hd v)
  have hd_pos : ∀ v, 0 < d v := fun v => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hd v)
  refine ⟨?_, ?_, ?_⟩
  ·
    have h := pageRank_iteration_bound α ε hα hε T d hd residual_norms h_nonneg
      vertices residual_vals h_select h_decrease
    linarith [h_init.symm ▸ h]
  ·
    exact pageRank_output_quality ε d r_final hd_pos h_term
  ·
    have h_vol := vol_supp_le_degree_sum d hd_nonneg p T vertices h_supp_covered
    have h_deg := pageRank_degree_sum_bound α ε hα T d residual_norms h_nonneg
      vertices residual_vals h_select h_decrease
    have hαε_pos : (0 : ℝ) < α * ε := mul_pos hα hε
    calc α * ε * vol d (vecSupp p)
      ≤ α * ε * ∑ i : Fin T, d (vertices i) := by
        gcongr
      _ ≤ residual_norms ⟨0, Nat.zero_lt_succ T⟩ := h_deg
      _ = 1 := h_init

end PageRank


-- created on 2026-10-23
