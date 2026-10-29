import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.StieltjesIntegral.Part2
open RiemannStieltjes


namespace RiemannStieltjes

/--
[taggedPartitionOfPartition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/StieltjesIntegral.lean)
-/
@[path]
lemma taggedPartitionOfPartition
  {a b : ℝ}
  {P : IntervalPartition a b} :
-- imply
  ∃ (PT : TaggedPartition a b), PT.toIntervalPartition = P :=
-- proof
  ⟨(⟨P,
      fun k => P.pts ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩,
      fun k => ⟨le_refl _, le_of_lt (P.strict_mono (Fin.mk_lt_mk.mpr (by omega)))⟩⟩ :
      TaggedPartition a b),
    rfl⟩

end RiemannStieltjes

namespace RiemannStieltjes

/--
[IntervalPartition.pts_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/StieltjesIntegral.lean)
-/
@[path]
lemma IntervalPartition.pts_mem_Icc
  {a b : ℝ}
  {P : IntervalPartition a b}
  (i : Fin (P.n + 1)) :
-- imply
  P.pts i ∈ Set.Icc a b :=
-- proof
  ⟨by calc a = P.pts ⟨0, Nat.zero_lt_succ P.n⟩ := P.first.symm
    _ ≤ P.pts i := P.strict_mono.monotone (Fin.zero_le i),
    by calc P.pts i ≤ P.pts ⟨P.n, Nat.lt_succ_iff.mpr le_rfl⟩ :=
      P.strict_mono.monotone (Fin.le_last i)
      _ = b := P.last⟩

end RiemannStieltjes

namespace RiemannStieltjes

/--
[commonRefinement](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/StieltjesIntegral.lean)
-/
@[path]
lemma commonRefinement
  {a b : ℝ}
  {P Q : IntervalPartition a b} :
-- imply
  ∃ R : IntervalPartition a b, R.IsRefinementOf P ∧ R.IsRefinementOf Q := by
-- proof
  set S := P.pointSet ∪ Q.pointSet
  have ha_mem : a ∈ S := Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
    ⟨⟨0, Nat.zero_lt_succ _⟩, Finset.mem_univ _, P.first⟩))
  have hb_mem : b ∈ S := Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
    ⟨⟨P.n, Nat.lt_succ_iff.mpr le_rfl⟩, Finset.mem_univ _, P.last⟩))
  have hab : a ≠ b := ne_of_lt
    (calc a = P.pts ⟨0, Nat.zero_lt_succ P.n⟩ := P.first.symm
      _ < P.pts ⟨P.n, Nat.lt_succ_iff.mpr le_rfl⟩ := P.strict_mono (Fin.mk_lt_mk.mpr P.hn)
      _ = b := P.last)
  have hcard : 2 ≤ S.card :=
    calc 2 = ({a, b} : Finset ℝ).card := by simp [hab]
      _ ≤ S.card := Finset.card_le_card (by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
  set m := S.card - 1
  have hm_pos : 0 < m := by omega
  have hcard_eq : S.card = m + 1 := by omega
  let φ := S.orderEmbOfFin hcard_eq
  have hmin : S.min' ⟨a, ha_mem⟩ = a := by
    apply le_antisymm
    · exact Finset.min'_le _ _ ha_mem
    · apply Finset.le_min'
      intro x hx
      obtain h | h := Finset.mem_union.mp hx
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h; exact (P.pts_mem_Icc i).1
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h; exact (Q.pts_mem_Icc i).1
  have hmax : S.max' ⟨a, ha_mem⟩ = b := by
    apply le_antisymm
    · apply Finset.max'_le
      intro x hx
      obtain h | h := Finset.mem_union.mp hx
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h; exact (P.pts_mem_Icc i).2
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h; exact (Q.pts_mem_Icc i).2
    · exact Finset.le_max' _ _ hb_mem
  have hφ_first : φ ⟨0, Nat.zero_lt_succ m⟩ = a := by
    rw [show φ = S.orderEmbOfFin hcard_eq from rfl,
      Finset.orderEmbOfFin_zero hcard_eq (by omega), hmin]
  have hφ_last : φ ⟨m, Nat.lt_succ_iff.mpr le_rfl⟩ = b := by
    have hfin : (⟨m, Nat.lt_succ_iff.mpr le_rfl⟩ : Fin (m + 1)) = ⟨m + 1 - 1, by omega⟩ := by
      simp
    rw [show φ = S.orderEmbOfFin hcard_eq from rfl, hfin,
      Finset.orderEmbOfFin_last hcard_eq (by omega), hmax]
  refine ⟨{
    n := m
    hn := hm_pos
    pts := φ
    first := hφ_first
    last := hφ_last
    strict_mono := φ.strictMono
  }, ?_, ?_⟩
  · intro j
    have : P.pts j ∈ Set.range φ := by
      rw [Finset.range_orderEmbOfFin S hcard_eq]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
    obtain ⟨i, hi⟩ := this
    exact ⟨i, hi⟩
  · intro j
    have : Q.pts j ∈ Set.range φ := by
      rw [Finset.range_orderEmbOfFin S hcard_eq]
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
    obtain ⟨i, hi⟩ := this
    exact ⟨i, hi⟩

end RiemannStieltjes

namespace RiemannStieltjes

/--
[hasStieltjesIntegral_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/StieltjesIntegral.lean)
-/
@[path]
lemma hasStieltjesIntegral_unique
  {a b : ℝ}
  [NormedField 𝕜]
  {f g : ℝ → 𝕜}
  {S₁ S₂ : 𝕜}
-- given
  (h₁ : HasStieltjesIntegral f g a b S₁)
  (h₂ : HasStieltjesIntegral f g a b S₂) :
-- imply
  S₁ = S₂ := by
-- proof
  by_contra h
  have hne : 0 < ‖S₁ - S₂‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero.mpr h
  have hε : (0 : ℝ) < ‖S₁ - S₂‖ / 2 := by linarith
  obtain ⟨P₁, hP₁⟩ := h₁ (‖S₁ - S₂‖ / 2) hε
  obtain ⟨P₂, hP₂⟩ := h₂ (‖S₁ - S₂‖ / 2) hε
  obtain ⟨R, hR₁, hR₂⟩ := commonRefinement P₁ P₂
  obtain ⟨PT, hPT⟩ := taggedPartitionOfPartition R
  have h₁' := hP₁ PT (by rw [hPT]; exact hR₁)
  have h₂' := hP₂ PT (by rw [hPT]; exact hR₂)
  have key : ‖S₁ - S₂‖ ≤ ‖stieltjesSum PT f g - S₁‖ + ‖stieltjesSum PT f g - S₂‖ := by
    calc ‖S₁ - S₂‖
      = ‖(S₁ - stieltjesSum PT f g) + (stieltjesSum PT f g - S₂)‖ := by ring_nf
      _ ≤ ‖S₁ - stieltjesSum PT f g‖ + ‖stieltjesSum PT f g - S₂‖ := norm_add_le _ _
      _ = ‖stieltjesSum PT f g - S₁‖ + ‖stieltjesSum PT f g - S₂‖ := by rw [norm_sub_rev]
  linarith

end RiemannStieltjes

namespace RiemannStieltjes

/--
[stieltjesIntegral_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/StieltjesIntegral.lean)
-/
@[path]
lemma stieltjesIntegral_spec
  {a b : ℝ}
  [NormedField 𝕜]
  {f g : ℝ → 𝕜}
-- given
  (h : StieltjesIntegrable f g a b) :
-- imply
  HasStieltjesIntegral f g a b (stieltjesIntegral f g a b) := by
-- proof
  unfold stieltjesIntegral
  rwa [dite_eq_left h]

end RiemannStieltjes

namespace RiemannStieltjes

/--
[IsRefinementOf.trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/StieltjesIntegral.lean)
-/
@[path]
lemma IsRefinementOf.trans
  {a b : ℝ}
  {P Q R : IntervalPartition a b}
-- given
  (hPQ : P.IsRefinementOf Q)
  (hQR : Q.IsRefinementOf R) :
-- imply
  P.IsRefinementOf R := by
-- proof
  intro j
  obtain ⟨i, hi⟩ := hQR j
  obtain ⟨k, hk⟩ := hPQ i
  exact ⟨k, by rw [hk, hi]⟩

end RiemannStieltjes

namespace RiemannStieltjes

/--
[IsRefinementOf.refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/StieltjesIntegral.lean)
-/
@[path]
lemma IsRefinementOf.refl
  {a b : ℝ}
  {P : IntervalPartition a b} :
-- imply
  P.IsRefinementOf P :=
-- proof
  fun j => ⟨j, rfl⟩

end RiemannStieltjes

namespace RiemannStieltjes

/--
[cumRefine_refines_prev](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/StieltjesIntegral.lean)
-/
@[path]
lemma cumRefine_refines_prev
  {a b : ℝ}
  {P : ℕ → IntervalPartition a b}
  {n : ℕ}
-- given
  (cr : ∀ Q R : IntervalPartition a b, ∃ S : IntervalPartition a b, S.IsRefinementOf Q ∧ S.IsRefinementOf R) :
-- imply
  (cumRefine P cr (n + 1)).IsRefinementOf (cumRefine P cr n) :=
-- proof
  (cr (cumRefine P cr n) (P (n + 1))).choose_spec.1

end RiemannStieltjes

namespace RiemannStieltjes

/--
[cumRefine_refines_P](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/StieltjesIntegral.lean)
-/
@[path]
lemma cumRefine_refines_P
  {a b : ℝ}
  {P : ℕ → IntervalPartition a b}
  {n : ℕ}
-- given
  (cr : ∀ Q R : IntervalPartition a b, ∃ S : IntervalPartition a b, S.IsRefinementOf Q ∧ S.IsRefinementOf R) :
-- imply
  (cumRefine P cr (n + 1)).IsRefinementOf (P (n + 1)) :=
-- proof
  (cr (cumRefine P cr n) (P (n + 1))).choose_spec.2

end RiemannStieltjes

namespace RiemannStieltjes

/--
[cumRefine_refines_P_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/StieltjesIntegral.lean)
-/
@[path]
lemma cumRefine_refines_P_le
  {a b : ℝ}
  {P : ℕ → IntervalPartition a b}
  {n k : ℕ}
-- given
  (cr : ∀ Q R : IntervalPartition a b, ∃ S : IntervalPartition a b, S.IsRefinementOf Q ∧ S.IsRefinementOf R)
  (hk : k ≤ n) :
-- imply
  (cumRefine P cr n).IsRefinementOf (P k) := by
-- proof
  induction n with
  | zero =>
    have : k = 0 := Nat.le_zero.mp hk
    subst this
    exact IsRefinementOf.refl _
  | succ n ih =>
    obtain rfl | hlt := Nat.eq_or_lt_of_le hk
    · exact cumRefine_refines_P P cr n
    · exact IsRefinementOf.trans (cumRefine_refines_prev P cr n) (ih (Nat.lt_succ_iff.mp hlt))

end RiemannStieltjes

namespace RiemannStieltjes

/--
[integrable_of_cauchy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/StieltjesIntegral.lean)
-/
@[path]
lemma integrable_of_cauchy
  {a b : ℝ}
  {f g : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hcauchy : ∀ ε > 0, ∃ P : IntervalPartition a b, ∀ PT₁ PT₂ : TaggedPartition a b, PT₁.toIntervalPartition.IsRefinementOf P → PT₂.toIntervalPartition.IsRefinementOf P → ‖stieltjesSum PT₁ f g - stieltjesSum PT₂ f g‖ < ε) :
-- imply
  StieltjesIntegrable f g a b := by
-- proof
  have hε : ∀ n : ℕ, (0 : ℝ) < 1 / (↑n + 1) := fun n => by positivity
  choose P_seq hP_seq using fun n => hcauchy (1 / (↑n + 1)) (hε n)
  let Q := cumRefine P_seq (fun P Q => commonRefinement P Q)
  choose PT_seq hPT_seq using fun n => taggedPartitionOfPartition (Q n)
  set s := fun n => stieltjesSum (PT_seq n) f g
  have hs_cauchy : CauchySeq s := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hN_pos : (0 : ℝ) < ↑N + 1 := by positivity
    have h_bound : 1 / (↑N + 1) < ε := by
      rw [div_lt_iff₀ hN_pos]
      calc 1 = ε * (1 / ε) := by field_simp
        _ < ε * (↑N + 1) := by nlinarith
    have hm_ref : (PT_seq m).toIntervalPartition.IsRefinementOf (P_seq N) := by
      rw [hPT_seq m]
      exact cumRefine_refines_P_le P_seq _ m N hm
    have hn_ref : (PT_seq n).toIntervalPartition.IsRefinementOf (P_seq N) := by
      rw [hPT_seq n]
      exact cumRefine_refines_P_le P_seq _ n N hn
    calc dist (s m) (s n) = ‖s m - s n‖ := by rw [Real.dist_eq, Real.norm_eq_abs]
      _ = ‖stieltjesSum (PT_seq m) f g - stieltjesSum (PT_seq n) f g‖ := rfl
      _ < 1 / (↑N + 1) := hP_seq N _ _ hm_ref hn_ref
      _ < ε := h_bound
  obtain ⟨S, hS⟩ := cauchySeq_tendsto_of_complete hs_cauchy
  refine ⟨S, fun ε hε => ?_⟩
  have hε_half : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (2 / ε)
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp hS) (ε / 2) hε_half
  set N := max N₁ N₂
  refine ⟨Q N, fun PT hPT => ?_⟩
  have hN₁_le : N₁ ≤ N := le_max_left _ _
  have hN₂_le : N₂ ≤ N := le_max_right _ _
  have hN_pos : (0 : ℝ) < ↑N₁ + 1 := by positivity
  have h1 : 1 / (↑N₁ + 1) < ε / 2 := by
    rw [div_lt_div_iff₀ hN_pos (by norm_num : (0 : ℝ) < 2)]
    have := (div_lt_iff₀ hε).mp hN₁
    nlinarith
  have hPT_ref_N : PT.toIntervalPartition.IsRefinementOf (P_seq N₁) :=
    IsRefinementOf.trans hPT (cumRefine_refines_P_le P_seq _ N N₁ hN₁_le)
  have hPTN_ref : (PT_seq N).toIntervalPartition.IsRefinementOf (P_seq N₁) := by
    rw [hPT_seq N]
    exact cumRefine_refines_P_le P_seq _ N N₁ hN₁_le
  have h_sum_close : ‖stieltjesSum PT f g - s N‖ < ε / 2 := by
    calc ‖stieltjesSum PT f g - s N‖
      = ‖stieltjesSum PT f g - stieltjesSum (PT_seq N) f g‖ := rfl
      _ < 1 / (↑N₁ + 1) := hP_seq N₁ _ _ hPT_ref_N hPTN_ref
      _ < ε / 2 := h1
  have h_seq_close : ‖s N - S‖ < ε / 2 := by
    rw [Real.norm_eq_abs, ← Real.dist_eq]
    exact hN₂ N hN₂_le
  calc ‖stieltjesSum PT f g - S‖
    = ‖(stieltjesSum PT f g - s N) + (s N - S)‖ := by ring_nf
    _ ≤ ‖stieltjesSum PT f g - s N‖ + ‖s N - S‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h_sum_close h_seq_close
    _ = ε := by ring

end RiemannStieltjes

namespace RiemannStieltjes

/--
[fin_sum_telescope](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/StieltjesIntegral.lean)
-/
@[path]
lemma fin_sum_telescope
  {_a _b : ℝ}
  {n : ℕ}
  {g : Fin (n + 1) → ℝ} :
-- imply
  ∑ i : Fin n, (g ⟨i.val + 1, by omega⟩ - g ⟨i.val, by omega⟩) = g ⟨n, by omega⟩ - g ⟨0, by omega⟩ := by
-- proof
  set h : ℕ → ℝ := fun i => g ⟨min i n, by omega⟩
  have hconv : ∀ (i : Fin n),
    g ⟨i.val + 1, by omega⟩ - g ⟨i.val, by omega⟩ = h (i.val + 1) - h i.val := by
    intro i
    simp only [h, min_eq_left (by omega : i.val ≤ n),
      min_eq_left (by omega : i.val + 1 ≤ n)]
  simp_rw [hconv]
  have hconv2 : (∑ i : Fin n, (h (i.val + 1) - h i.val)) =
    ∑ i ∈ Finset.range n, (h (i + 1) - h i) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi; rw [dite_eq_left (Finset.mem_range.mp hi)]
  rw [hconv2, Finset.sum_range_sub]
  simp only [h, min_self, Nat.zero_min]

end RiemannStieltjes


-- created on 2026-10-23
-- updated on 2026-10-28
