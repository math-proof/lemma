import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Choose.Multinomial
import Lemma.Finset.CardFilterUniv.le.PowAdd_1Card
import Lemma.Real.AbsAddMulInvLogSum_MulDivLog.le.DivMulCardAddDivLog2'1.of.All_Gt_0.EqSum.Gt_0
open Finset Real


private lemma coord_lt [Fintype α] (n : ℕ) (c : α → ℕ) (h : ∑ i, c i = n) (a : α) : c a < n + 1 := by
  apply Nat.lt_succ_of_le
  rw [← h]
  apply single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ a)

private noncomputable def typeMass {α : Type*} [Fintype α] (μ : α → ℝ) (c : α → ℕ) : ℝ :=
  (Nat.multinomial univ c : ℝ) * ∏ a, μ a ^ c a

private noncomputable def typeKL {α : Type*} [Fintype α] (n : ℕ) (μ : α → ℝ) (c : α → ℕ) : ℝ :=
  ∑ a, ((c a : ℝ) / n) * log (((c a : ℝ) / n) / μ a)

private def toFin [Fintype α] (n : ℕ) (c : α → ℕ) : α → Fin (n + 1) :=
  fun a => if h : ∑ i, c i = n then ⟨c a, coord_lt n c h a⟩ else ⟨0, Nat.succ_pos n⟩

private lemma toFin_val [Fintype α] {n : ℕ} {c : α → ℕ} (h : ∑ i, c i = n) (a : α) : (toFin n c a).1 = c a := by
  simp [toFin, h]

private lemma card_le_pow [Fintype α] [DecidableEq α] {n : ℕ} {s : Finset (α → ℕ)} (hs : ∀ c ∈ s, ∑ a, c a = n) :
  #s ≤ (n + 1) ^ Fintype.card α := by
  have hinj : Set.InjOn (toFin n) (s : Set (α → ℕ)) := by
    intro c hc d hd hcd
    funext a
    rw [← toFin_val (hs c hc) a, ← toFin_val (hs d hd) a]
    exact Fin.val_eq_of_eq (congr_fun hcd a)
  refine le_trans ?_ (CardFilterUniv.le.PowAdd_1Card n)
  rw [← card_image_of_injOn hinj]
  apply card_le_card
  intro c hc
  obtain ⟨d, hd, rfl⟩ := mem_image.mp hc
  refine mem_filter.mpr ⟨mem_univ _, ?_⟩
  simp [toFin, hs d hd]

private lemma typeMass_pos [Fintype α] {μ : α → ℝ} {c : α → ℕ} (hμ : ∀ a, 0 < c a → 0 < μ a) : 0 < typeMass μ c := by
  unfold typeMass
  apply mul_pos
  ·
    exact_mod_cast Nat.multinomial_pos univ c
  ·
    refine Finset.prod_pos fun a _ => ?_
    if ha : c a = 0 then
      simp [ha]
    else
      exact pow_pos (hμ a (Nat.pos_of_ne_zero ha)) (c a)

private lemma abs_log_union [Fintype α] [DecidableEq α] {n : ℕ} {s : Finset (α → ℕ)} {μ : α → ℝ} (hn : 0 < n) (hs : ∀ c ∈ s, ∑ a, c a = n) (hne : s.Nonempty) (hμ : ∀ c ∈ s, ∀ a, 0 < c a → 0 < μ a) :
  |(n : ℝ)⁻¹ * log (∑ c ∈ s, typeMass μ c) + s.inf' hne (typeKL n μ)| ≤
    (Fintype.card α : ℝ) * (log (n + 1) + log n / 2 + 1) / n := by
  let f := typeMass μ
  let kl := typeKL n μ
  have hpos : ∀ c ∈ s, 0 < f c := fun c hc => typeMass_pos (hμ c hc)
  obtain ⟨cMin, hcMin, hklMin⟩ := exists_mem_eq_inf' (H := hne) kl
  obtain ⟨cMax, hcMax, hfMax⟩ := exists_mem_eq_sup' (H := hne) f
  have hsumpos : 0 < ∑ c ∈ s, f c := by
    apply lt_of_lt_of_le (hpos cMin hcMin)
    apply single_le_sum (fun c hc => (hpos c hc).le) hcMin
  have hsuppos : 0 < s.sup' hne f := by
    rw [hfMax]
    exact hpos cMax hcMax
  have hcardpos : (0 : ℝ) < #s := by exact_mod_cast hne.card_pos
  have hcardle : (#s : ℝ) ≤ (n + 1 : ℝ) ^ Fintype.card α := by
    exact_mod_cast card_le_pow hs
  have hlogCard : log (#s : ℝ) ≤ (Fintype.card α : ℝ) * log (n + 1) := by
    have hbase : (0 : ℝ) < (n + 1 : ℝ) ^ Fintype.card α := by positivity
    have := log_le_log hcardpos hcardle
    simpa [log_pow] using this
  have hsumle : ∑ c ∈ s, f c ≤ (#s : ℝ) * s.sup' hne f := by
    have := sum_le_card_nsmul s f (s.sup' hne f) (fun c hc => le_sup' f hc)
    simpa [nsmul_eq_mul] using this
  have hlogSum : log (∑ c ∈ s, f c) ≤ log (#s : ℝ) + log (s.sup' hne f) := by
    have hmul : 0 < (#s : ℝ) * s.sup' hne f := mul_pos hcardpos hsuppos
    have := log_le_log hsumpos hsumle
    rwa [log_mul (by exact_mod_cast hne.card_pos.ne') hsuppos.ne'] at this
  have hrate (c : α → ℕ) (hc : c ∈ s) :
    |(n : ℝ)⁻¹ * log (f c) + kl c| ≤ (Fintype.card α : ℝ) * (log n / 2 + 1) / n := by
    simpa [f, kl, typeMass, typeKL] using
      AbsAddMulInvLogSum_MulDivLog.le.DivMulCardAddDivLog2'1.of.All_Gt_0.EqSum.Gt_0
        hn (hs c hc) (hμ c hc)
  have hsmall : (Fintype.card α : ℝ) * (log n / 2 + 1) / n ≤
      (Fintype.card α : ℝ) * (log (n + 1) + log n / 2 + 1) / n := by
    have hlog1 : 0 ≤ log (n + 1 : ℝ) :=
      log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    refine div_le_div_of_nonneg_right ?_ (by exact_mod_cast hn.le)
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity : (0 : ℝ) ≤ Fintype.card α)
  apply abs_le.mpr ⟨_, _⟩
  ·
    have hterm : log (f cMin) ≤ log (∑ c ∈ s, f c) := by
      apply log_le_log (hpos cMin hcMin)
      apply single_le_sum (fun c hc => (hpos c hc).le) hcMin
    have hnneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
    have hmul : (n : ℝ)⁻¹ * log (f cMin) ≤ (n : ℝ)⁻¹ * log (∑ c ∈ s, f c) :=
      mul_le_mul_of_nonneg_left hterm hnneg
    have habs := (abs_le.mp (hrate cMin hcMin)).1
    calc
      _ ≤ -((Fintype.card α : ℝ) * (log n / 2 + 1) / n) := neg_le_neg hsmall
      _ ≤ (n : ℝ)⁻¹ * log (f cMin) + kl cMin := habs
      _ ≤ (n : ℝ)⁻¹ * log (∑ c ∈ s, f c) + kl cMin := add_le_add_left hmul _
      _ = (n : ℝ)⁻¹ * log (∑ c ∈ s, f c) + s.inf' hne kl := by rw [hklMin]
  ·
    have hlogSup : log (s.sup' hne f) = log (f cMax) := by rw [hfMax]
    have habs := (abs_le.mp (hrate cMax hcMax)).2
    have hklLe : s.inf' hne kl ≤ kl cMax := inf'_le kl hcMax
    have hnneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
    have hdiv : (n : ℝ)⁻¹ * log (∑ c ∈ s, f c) ≤ (n : ℝ)⁻¹ * (log (#s : ℝ) + log (s.sup' hne f)) :=
      mul_le_mul_of_nonneg_left hlogSum hnneg
    have hcardPart : (n : ℝ)⁻¹ * log (#s : ℝ) ≤ (n : ℝ)⁻¹ * ((Fintype.card α : ℝ) * log (n + 1)) :=
      mul_le_mul_of_nonneg_left hlogCard hnneg
    have htail : (n : ℝ)⁻¹ * log (f cMax) + s.inf' hne kl ≤ (Fintype.card α : ℝ) * (log n / 2 + 1) / n :=
      (add_le_add_right hklLe _).trans habs
    calc
      _ ≤ (n : ℝ)⁻¹ * (log (#s : ℝ) + log (s.sup' hne f)) + s.inf' hne kl :=
        add_le_add_left hdiv _
      _ = (n : ℝ)⁻¹ * log (#s : ℝ) + ((n : ℝ)⁻¹ * log (s.sup' hne f) + s.inf' hne kl) := by
        ring
      _ ≤ (n : ℝ)⁻¹ * ((Fintype.card α : ℝ) * log (n + 1)) + ((n : ℝ)⁻¹ * log (f cMax) + s.inf' hne kl) := by
        rw [hlogSup]
        apply add_le_add_left hcardPart
      _ ≤ (n : ℝ)⁻¹ * ((Fintype.card α : ℝ) * log (n + 1)) + (Fintype.card α : ℝ) * (log n / 2 + 1) / n :=
        add_le_add_right htail _
      _ = (Fintype.card α : ℝ) * (log (n + 1) + log n / 2 + 1) / n := by
        ring

/--
A nonempty union of empirical counts on a finite alphabet has logarithmic total mass
`-inf KL(c/n ‖ μ)`, up to `|α| (log (n + 1) + log n / 2 + 1) / n`.
The `(n + 1) ^ |α|` types contribute only `log (n + 1)`, which is `o(n)`.
-/
@[path]
private lemma main
  [Fintype α] [DecidableEq α]
  {n : ℕ} {s : Finset (α → ℕ)} {μ : α → ℝ}
-- given
  (hn : 0 < n)
  (hs : ∀ c ∈ s, ∑ a, c a = n)
  (hne : s.Nonempty)
  (hμ : ∀ c ∈ s, ∀ a, 0 < c a → 0 < μ a) :
-- imply
  |(n : ℝ)⁻¹ * log (∑ c ∈ s, (Nat.multinomial univ c : ℝ) * ∏ a, μ a ^ c a) + s.inf' hne (fun c => ∑ a, ((c a : ℝ) / n) * log (((c a : ℝ) / n) / μ a))| ≤
    (Fintype.card α : ℝ) * (log (n + 1) + log n / 2 + 1) / n :=
-- proof
  abs_log_union hn hs hne hμ


-- created on 2026-11-02

