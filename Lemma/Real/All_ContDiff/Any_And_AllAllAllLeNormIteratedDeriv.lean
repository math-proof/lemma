import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private noncomputable def dU
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (G : E × ℝ → F) (n : ℕ) : E × ℝ → F :=
  Nat.rec G (fun _ ih p => fderiv ℝ ih p (0, 1)) n

private lemma contDiff_dU
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : E × ℝ → F}
  -- given
  (hG : ContDiff ℝ (⊤ : ENat) G) :
  -- imply
  ∀ n, ContDiff ℝ (⊤ : ENat) (dU G n) := by
  -- proof
  intro n
  induction n
  · apply hG
  ·
    rename_i n ih
    show ContDiff ℝ (⊤ : ENat) (fun p => fderiv ℝ (dU G n) p (0, 1))
    apply (ih.fderiv_right (by simp)).clm_apply contDiff_const

private lemma iteratedDeriv_slice
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : E × ℝ → F}
  -- given
  (hG : ContDiff ℝ (⊤ : ENat) G) :
  -- imply
  ∀ (n : ℕ) (a : E) (u : ℝ), iteratedDeriv n (fun u => G (a, u)) u = dU G n (a, u) := by
  -- proof
  intro n
  induction n
  ·
    intro a u
    rfl
  ·
    rename_i n ih
    intro a u
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv n (fun u => G (a, u)) = fun u => dU G n (a, u) := funext (ih a)
    rw [hfun]
    show deriv (fun u => dU G n (a, u)) u = fderiv ℝ (dU G n) (a, u) (0, 1)
    apply ((((contDiff_dU hG n).differentiable (by simp)).differentiableAt).hasFDerivAt.comp_hasDerivAt u ((hasDerivAt_const u a).prodMk (hasDerivAt_id u))).deriv

private lemma helper_main
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ψ : E → ℝ → F}
  {S : Set E}
  {R : ℝ}
  {N : ℕ}
  -- given
  (hΨ : ContDiff ℝ (⊤ : ENat) (fun p : E × ℝ => Ψ p.1 p.2))
  (hS : IsCompact S) :
  -- imply
  (∀ a : E, ContDiff ℝ N (Ψ a)) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ S, ∀ u ∈ Set.Icc (-R) R, ∀ n ≤ N, ‖iteratedDeriv n (Ψ a) u‖ ≤ C := by
  -- proof
  set G : E × ℝ → F := fun p => Ψ p.1 p.2
  have hslice : ∀ a : E, ContDiff ℝ (⊤ : ENat) (Ψ a) := fun a => by
    have : Ψ a = G ∘ fun u : ℝ => ((a, u) : E × ℝ) := rfl
    rw [this]
    apply hΨ.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨fun a => (hslice a).of_le (by exact_mod_cast le_top), ?_⟩
  have hK : IsCompact (S ×ˢ Set.Icc (-R) R) := hS.prod isCompact_Icc
  have hb : ∀ n : ℕ, ∃ Cn : ℝ, ∀ p ∈ S ×ˢ Set.Icc (-R) R, ‖dU G n p‖ ≤ Cn := fun n => hK.exists_bound_of_continuousOn ((contDiff_dU hΨ n).continuous.continuousOn)
  choose Cn hCn using hb
  refine ⟨∑ n ∈ Finset.range (N + 1), |Cn n|, Finset.sum_nonneg fun n _ => abs_nonneg _, ?_⟩
  intro a ha u hu n hn
  have hmem : ((a, u) : E × ℝ) ∈ S ×ˢ Set.Icc (-R) R := ⟨ha, hu⟩
  have h1 : ‖iteratedDeriv n (Ψ a) u‖ ≤ |Cn n| := by
    rw [show Ψ a = fun u => G (a, u) from rfl, iteratedDeriv_slice hΨ n a u]
    apply (hCn n _ hmem).trans (le_abs_self _)
  refine h1.trans ?_
  apply Finset.single_le_sum (f := fun n => |Cn n|) (fun n _ => abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

/--
[ContDiff_exists_forall_norm_iteratedDeriv_slice_le_of_isCompact](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ContDiff_exists_forall_norm_iteratedDeriv_slice_le_of_isCompact.lean)
-/
@[path]
private lemma main
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ψ : E → ℝ → F}
  {S : Set E}
  {R : ℝ}
  {N : ℕ}
  -- given
  (hΨ : ContDiff ℝ (⊤ : ENat) (fun p : E × ℝ => Ψ p.1 p.2))
  (hS : IsCompact S) :
  -- imply
  (∀ a : E, ContDiff ℝ N (Ψ a)) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ S, ∀ u ∈ Set.Icc (-R) R, ∀ n ≤ N, ‖iteratedDeriv n (Ψ a) u‖ ≤ C := by
  -- proof
  apply helper_main hΨ hS


-- created on 2026-10-20
