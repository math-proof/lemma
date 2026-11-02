import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Multinomial
import Initialize.Tactic.Attr.Basic
open Finset Real Stirling
open scoped Nat


/-- `n * H(c/n)`, with the convention `0 * log 0 = 0`. -/
private noncomputable def countLog {α : Type*} [Fintype α] [DecidableEq α] (n : ℕ) (c : α → ℕ) : ℝ :=
  ∑ a, (c a : ℝ) * log ((n : ℝ) / c a)

/-- Empirical Kullback–Leibler divergence `KL(c/n ‖ μ)`. -/
private noncomputable def empiricalKL {α : Type*} [Fintype α] [DecidableEq α] (n : ℕ) (c : α → ℕ) (μ : α → ℝ) : ℝ :=
  ∑ a, ((c a : ℝ) / n) * log (((c a : ℝ) / n) / μ a)

private lemma stirlingSeq_le_one {n : ℕ} (hn : n ≠ 0) : stirlingSeq n ≤ exp 1 / √2 := by
  have hn1 : n = (n - 1) + 1 := by omega
  rw [hn1]
  simpa [stirlingSeq_one] using stirlingSeq'_antitone (Nat.zero_le (n - 1))

private lemma log_factorial_le {n : ℕ} (hn : n ≠ 0) :
  log (n ! : ℝ) ≤ n * log n - n + log n / 2 + 1 := by
  have hseq : stirlingSeq n ≤ exp 1 / √2 := stirlingSeq_le_one hn
  have hpos : 0 < stirlingSeq n := by
    have hn1 : n = (n - 1) + 1 := by omega
    rw [hn1]
    exact stirlingSeq'_pos (n - 1)
  have hden : √(2 * (n : ℝ)) * ((n : ℝ) / exp 1) ^ n ≠ 0 := by positivity
  have hmul : stirlingSeq n * (√(2 * (n : ℝ)) * ((n : ℝ) / exp 1) ^ n) = (n ! : ℝ) := by
    rw [stirlingSeq]
    field_simp
  have hlog : log (n ! : ℝ) =
      log (stirlingSeq n) + log (√(2 * (n : ℝ))) + n * log ((n : ℝ) / exp 1) := by
    rw [← hmul, log_mul hpos.ne' hden, log_mul (by positivity) (by positivity), log_pow]
    ring
  rw [hlog, log_sqrt (by positivity), log_mul (by positivity) (by positivity),
    log_div (by positivity) (by positivity), log_exp]
  have hlogSeq : log (stirlingSeq n) ≤ 1 - log 2 / 2 := calc
    _ ≤ log (exp 1 / √2) := log_le_log hpos hseq
    _ = log (exp 1) - log (√2) := by
      rw [log_div (by positivity) (by positivity)]
    _ = 1 - log 2 / 2 := by
      rw [log_exp, log_sqrt (by positivity)]
  linarith [hlogSeq]

private lemma log_factorial_le_of_count (m : ℕ) :
  log (m ! : ℝ) ≤ if m = 0 then 0 else (m : ℝ) * log m - m + log m / 2 + 1 := by
  if hm : m = 0 then
    simp [hm]
  else
    simp [hm]
    exact log_factorial_le hm

private lemma log_factorial_ge_of_count (m : ℕ) :
  (if m = 0 then 0 else (m : ℝ) * log m - m + log m / 2 + log (2 * π) / 2) ≤ log (m ! : ℝ) := by
  if hm : m = 0 then
    simp [hm]
  else
    simp [hm]
    exact le_log_factorial_stirling hm

private lemma log_multinomial_eq {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (c : α → ℕ) (hsum : ∑ a, c a = n) :
  log (Nat.multinomial univ c : ℝ) = log (n ! : ℝ) - ∑ a, log ((c a)! : ℝ) := by
  have hspec := Nat.multinomial_spec univ c
  rw [hsum] at hspec
  have hmul : (∏ a, ((c a)! : ℝ)) * (Nat.multinomial univ c : ℝ) = (n ! : ℝ) := by
    exact_mod_cast hspec
  have hprod : (∏ a, ((c a)! : ℝ)) ≠ 0 := by positivity
  have hmult : (Nat.multinomial univ c : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos univ c).ne'
  rw [← hmul, log_mul hprod hmult, log_prod (fun a _ => by positivity)]
  ring

private lemma countLog_eq {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (c : α → ℕ) (hn : 0 < n) (hsum : ∑ a, c a = n) :
  countLog n c =
    n * log n - ∑ a ∈ univ.filter (fun a => 0 < c a), (c a : ℝ) * log (c a) := by
  unfold countLog
  have hterm : ∀ a, (c a : ℝ) * log ((n : ℝ) / c a) =
      if 0 < c a then (c a : ℝ) * log n - (c a : ℝ) * log (c a) else 0 := by
    intro a
    if ha : 0 < c a then
      have hdiv : log ((n : ℝ) / c a) = log n - log (c a) :=
        log_div (by exact_mod_cast hn.ne') (by exact_mod_cast ha.ne')
      simp [ha, hdiv, mul_sub]
    else
      have : c a = 0 := Nat.eq_zero_of_not_pos ha
      simp [this]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  have hmass : ∑ a ∈ univ.filter (fun a => 0 < c a), (c a : ℝ) = n := by
    have hsubset : ∑ a ∈ univ.filter (fun a => 0 < c a), (c a : ℝ) = ∑ a, (c a : ℝ) := by
      refine Finset.sum_subset (filter_subset _ univ) ?_
      intro a _ hnot
      have : ¬ 0 < c a := by simpa [mem_filter] using hnot
      simp [Nat.eq_zero_of_not_pos this]
    rw [hsubset]
    exact_mod_cast hsum
  calc
    _ = ∑ a ∈ univ.filter (fun a => 0 < c a), (c a : ℝ) * log n -
        ∑ a ∈ univ.filter (fun a => 0 < c a), (c a : ℝ) * log (c a) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ a ∈ univ.filter (fun a => 0 < c a), (c a : ℝ)) * log n -
        ∑ a ∈ univ.filter (fun a => 0 < c a), (c a : ℝ) * log (c a) := by
      rw [← Finset.sum_mul]
    _ = n * log n - ∑ a ∈ univ.filter (fun a => 0 < c a), (c a : ℝ) * log (c a) := by
      rw [hmass]

private lemma sum_affine {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) (f g h : α → ℝ) (k : ℝ) :
  ∑ a ∈ s, (f a - g a + h a / 2 + k) =
    (∑ a ∈ s, f a) - ∑ a ∈ s, g a + (∑ a ∈ s, h a) / 2 + s.card * k := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    simp [ha, ih, Finset.sum_insert, Finset.card_insert_of_notMem]
    ring

private lemma abs_log_multinomial_sub_countLog {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (c : α → ℕ) (hn : 0 < n) (hsum : ∑ a, c a = n) :
  |log (Nat.multinomial univ c : ℝ) - countLog n c| ≤
    (Fintype.card α : ℝ) * (log n / 2 + 1) := by
  let pos := univ.filter (fun a => 0 < c a)
  have hS : countLog n c = n * log n - ∑ a ∈ pos, (c a : ℝ) * log (c a) := countLog_eq c hn hsum
  have hsumc : ∑ a ∈ pos, (c a : ℝ) = n := by
    have hsubset : ∑ a ∈ pos, (c a : ℝ) = ∑ a, (c a : ℝ) := by
      refine Finset.sum_subset (filter_subset _ univ) ?_
      intro a _ hnot
      have : ¬ 0 < c a := by simpa [pos, mem_filter] using hnot
      simp [Nat.eq_zero_of_not_pos this]
    rw [hsubset]
    exact_mod_cast hsum
  have hcardPos : (pos.card : ℝ) ≤ Fintype.card α := by
    exact_mod_cast Finset.card_filter_le univ (fun a => 0 < c a)
  have hcard1 : (1 : ℝ) ≤ Fintype.card α := by
    have hex : ∃ a, 0 < c a := by
      by_contra h
      have h0 : ∀ a, c a = 0 := by
        intro a
        exact Nat.eq_zero_of_not_pos fun ha => h ⟨a, ha⟩
      have : ∑ a, c a = 0 := Finset.sum_eq_zero fun a _ => h0 a
      omega
    have : Nonempty α := ⟨hex.choose⟩
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero)
  have hlogc : ∑ a ∈ pos, log (c a : ℝ) ≤ (pos.card : ℝ) * log n := by
    have hle : ∀ a ∈ pos, log (c a : ℝ) ≤ log (n : ℝ) := by
      intro a ha
      exact log_le_log (by exact_mod_cast (mem_filter.mp ha).2) (by exact_mod_cast (hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ a)))
    have := Finset.sum_le_sum hle
    simpa [pos, Finset.sum_const, nsmul_eq_mul] using this
  have hBnonneg : 0 ≤ log (n : ℝ) / 2 + 1 := by
    have : 0 ≤ log (n : ℝ) := log_nonneg (by exact_mod_cast hn)
    linarith
  have hzeros : ∑ a, log ((c a)! : ℝ) = ∑ a ∈ pos, log ((c a)! : ℝ) := by
    symm
    refine Finset.sum_subset (filter_subset _ univ) ?_
    intro a _ hnot
    have : c a = 0 := Nat.eq_zero_of_not_pos (by simpa [pos, mem_filter] using hnot)
    simp [this]
  let f := fun a => (c a : ℝ) * log (c a)
  let g := fun a => (c a : ℝ)
  let hlog := fun a => log (c a : ℝ)
  have hUpper : ∑ a ∈ pos, (f a - g a + hlog a / 2 + 1) =
      (∑ a ∈ pos, f a) - n + (∑ a ∈ pos, hlog a) / 2 + pos.card := by
    rw [sum_affine pos f g hlog 1, hsumc]
    ring
  have hLower : ∑ a ∈ pos, (f a - g a + hlog a / 2 + log (2 * π) / 2) =
      (∑ a ∈ pos, f a) - n + (∑ a ∈ pos, hlog a) / 2 + pos.card * (log (2 * π) / 2) := by
    rw [sum_affine pos f g hlog (log (2 * π) / 2), hsumc]
  have hsumLogLe : ∑ a, log ((c a)! : ℝ) ≤ ∑ a ∈ pos, (f a - g a + hlog a / 2 + 1) := by
    rw [hzeros]
    refine Finset.sum_le_sum fun a ha => ?_
    have hca : 0 < c a := (mem_filter.mp ha).2
    have hle := log_factorial_le_of_count (c a)
    rw [ite_eq_right hca.ne'] at hle
    simpa [f, g, hlog] using hle
  have hsumLogGe : ∑ a ∈ pos, (f a - g a + hlog a / 2 + log (2 * π) / 2) ≤ ∑ a, log ((c a)! : ℝ) := by
    rw [hzeros]
    refine Finset.sum_le_sum fun a ha => ?_
    have hca : 0 < c a := (mem_filter.mp ha).2
    have hge := log_factorial_ge_of_count (c a)
    rw [ite_eq_right hca.ne'] at hge
    simpa [f, g, hlog] using hge
  have hlow : countLog n c - (Fintype.card α : ℝ) * (log n / 2 + 1) ≤
      log (Nat.multinomial univ c : ℝ) := by
    rw [log_multinomial_eq c hsum]
    have hnle := le_log_factorial_stirling (Nat.pos_iff_ne_zero.mp hn)
    have hdiff : (n : ℝ) * log n - n + log n / 2 + log (2 * π) / 2 -
        ∑ a ∈ pos, (f a - g a + hlog a / 2 + 1) ≤
        log (n ! : ℝ) - ∑ a, log ((c a)! : ℝ) := by
      linarith
    rw [hUpper] at hdiff
    have hrest : countLog n c + log n / 2 - (∑ a ∈ pos, hlog a) / 2 + log (2 * π) / 2 - pos.card ≤
        log (n ! : ℝ) - ∑ a, log ((c a)! : ℝ) := by
      rw [hS] at *
      linarith
    have hdrop : countLog n c - (pos.card : ℝ) * (log n / 2 + 1) ≤
        countLog n c + log n / 2 - (∑ a ∈ pos, hlog a) / 2 + log (2 * π) / 2 - pos.card := by
      have hπ : (3 : ℝ) < π := Real.pi_gt_three
      have hhalf : 0 ≤ log (2 * π) := log_nonneg (by linarith)
      have hsumle : ∑ a ∈ pos, hlog a ≤ (pos.card : ℝ) * log n := hlogc
      have hlogn : 0 ≤ log (n : ℝ) := log_nonneg (by exact_mod_cast (Nat.one_le_of_lt hn))
      nlinarith
    have hcard : (pos.card : ℝ) * (log n / 2 + 1) ≤ (Fintype.card α : ℝ) * (log n / 2 + 1) :=
      mul_le_mul_of_nonneg_right hcardPos hBnonneg
    linarith
  have hup : log (Nat.multinomial univ c : ℝ) ≤
      countLog n c + (Fintype.card α : ℝ) * (log n / 2 + 1) := by
    rw [log_multinomial_eq c hsum]
    have hnle := log_factorial_le (Nat.pos_iff_ne_zero.mp hn)
    have hdiff : log (n ! : ℝ) - ∑ a, log ((c a)! : ℝ) ≤
        (n : ℝ) * log n - n + log n / 2 + 1 -
          ∑ a ∈ pos, (f a - g a + hlog a / 2 + log (2 * π) / 2) := by
      linarith
    rw [hLower] at hdiff
    have hrest : log (n ! : ℝ) - ∑ a, log ((c a)! : ℝ) ≤
        countLog n c + log n / 2 + 1 := by
      have hπ : (3 : ℝ) < π := Real.pi_gt_three
      have hnn : 0 ≤ (∑ a ∈ pos, hlog a) / 2 := by
        refine div_nonneg ?_ (by norm_num)
        refine Finset.sum_nonneg fun a ha => ?_
        exact log_nonneg (by exact_mod_cast (Nat.one_le_of_lt (mem_filter.mp ha).2))
      have hpi : 0 ≤ (pos.card : ℝ) * (log (2 * π) / 2) := by
        refine mul_nonneg (Nat.cast_nonneg _) ?_
        exact div_nonneg (log_nonneg (by linarith)) (by norm_num)
      rw [hS]
      linarith
    have hone : log n / 2 + 1 ≤ (Fintype.card α : ℝ) * (log n / 2 + 1) := by
      have := mul_le_mul_of_nonneg_right hcard1 hBnonneg
      simpa using this
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma log_prod_pow {α : Type*} [Fintype α] [DecidableEq α] (μ : α → ℝ) (c : α → ℕ) (hμ : ∀ a, 0 < c a → 0 < μ a) :
  log (∏ a, μ a ^ c a) = ∑ a, (c a : ℝ) * log (μ a) := by
  have hne : ∀ a ∈ univ, μ a ^ c a ≠ 0 := by
    intro a _
    if ha : c a = 0 then
      simp [ha]
    else
      exact (pow_pos (hμ a (Nat.pos_of_ne_zero ha)) (c a)).ne'
  rw [log_prod hne, Finset.sum_congr rfl fun a _ => log_pow (μ a) (c a)]

private lemma empiricalKL_eq {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (c : α → ℕ) (μ : α → ℝ) (hn : 0 < n) (hμ : ∀ a, 0 < c a → 0 < μ a) :
  empiricalKL n c μ = -countLog n c / n - ∑ a, ((c a : ℝ) / n) * log (μ a) := by
  have hpoint : ∀ a, ((c a : ℝ) / n) * log (((c a : ℝ) / n) / μ a) =
      -((c a : ℝ) * log ((n : ℝ) / c a)) / n - ((c a : ℝ) / n) * log (μ a) := by
    intro a
    if ha : 0 < c a then
      have hμa : 0 < μ a := hμ a ha
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hc0 : (c a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
      have hdivμ : log (((c a : ℝ) / n) / μ a) = log ((c a : ℝ) / n) - log (μ a) :=
        log_div (div_ne_zero hc0 hn0) hμa.ne'
      have hdivc : log ((n : ℝ) / c a) = -log ((c a : ℝ) / n) := by
        rw [log_div hn0 hc0, log_div hc0 hn0]
        ring
      rw [hdivμ, hdivc]
      ring
    else
      have : c a = 0 := Nat.eq_zero_of_not_pos ha
      simp [this]
  simp only [empiricalKL, countLog, hpoint, Finset.sum_sub_distrib]
  have hdiv : ∑ x, (-((c x : ℝ) * log ((n : ℝ) / c x))) / n =
      (-∑ a, (c a : ℝ) * log ((n : ℝ) / c a)) / n := by
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
  rw [hdiv]

private lemma abs_log_multinomial_kl {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (c : α → ℕ) (μ : α → ℝ) (hn : 0 < n) (hsum : ∑ a, c a = n) (hμ : ∀ a, 0 < c a → 0 < μ a) :
  |(n : ℝ)⁻¹ * log ((Nat.multinomial univ c : ℝ) * ∏ a, μ a ^ c a) + empiricalKL n c μ| ≤
    (Fintype.card α : ℝ) * (log n / 2 + 1) / n := by
  have hmult : (Nat.multinomial univ c : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos univ c).ne'
  have hprod : (∏ a, μ a ^ c a) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
    if ha : c a = 0 then
      simp [ha]
    else
      exact (pow_pos (hμ a (Nat.pos_of_ne_zero ha)) (c a)).ne'
  rw [log_mul hmult hprod, log_prod_pow μ c hμ]
  have hkl := empiricalKL_eq c μ hn hμ
  have habs := abs_log_multinomial_sub_countLog c hn hsum
  have heq : (n : ℝ)⁻¹ * (log (Nat.multinomial univ c : ℝ) + ∑ a, (c a : ℝ) * log (μ a)) + empiricalKL n c μ = (log (Nat.multinomial univ c : ℝ) - countLog n c) / n := by
    rw [hkl, mul_add, Finset.mul_sum]
    have hdiv : ∑ a, (n : ℝ)⁻¹ * ((c a : ℝ) * log (μ a)) = ∑ a, ((c a : ℝ) / n) * log (μ a) := by
      refine Finset.sum_congr rfl fun _ _ => ?_
      ring
    rw [hdiv]
    ring
  rw [heq, abs_div, abs_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)]
  exact div_le_div_of_nonneg_right habs (by exact_mod_cast hn.le)

/--
One empirical count of an i.i.d. finite-alphabet sample has logarithmic probability
`-KL(c/n ‖ μ)`, up to the Stirling error `|α| (log n / 2 + 1) / n`.
-/
@[path]
private lemma main
  [Fintype α] [DecidableEq α]
  {n : ℕ} {c : α → ℕ} {μ : α → ℝ}
-- given
  (hn : 0 < n)
  (h : ∑ a, c a = n)
  (hμ : ∀ a, 0 < c a → 0 < μ a) :
-- imply
  |(n : ℝ)⁻¹ * log ((Nat.multinomial univ c : ℝ) * ∏ a, μ a ^ c a) + ∑ a, ((c a : ℝ) / n) * log (((c a : ℝ) / n) / μ a)| ≤
    (Fintype.card α : ℝ) * (log n / 2 + 1) / n := by
-- proof
  simpa [empiricalKL] using abs_log_multinomial_kl c μ hn h hμ


-- created on 2026-11-02

