import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.InformationTheory.ShannonSourceCoding
open Real BigOperators Finset
open MathlibExt.InformationTheory.ShannonSourceCodingWanted


namespace MathlibExt.InformationTheory.ShannonSourceCodingWanted

/--
[pmf_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/ShannonSourceCoding.lean)
-/
@[path]
private lemma pmf_le_one {α : Type*} [Fintype α]
  (p : α → ℝ) (hp_pos : ∀ a, 0 < p a) (hp_sum : ∑ a : α, p a = 1) (a : α) :
  p a ≤ 1 := by
  calc p a ≤ ∑ a : α, p a :=
    Finset.single_le_sum (fun i _ => le_of_lt (hp_pos i)) (Finset.mem_univ a)
    _ = 1 := hp_sum

end MathlibExt.InformationTheory.ShannonSourceCodingWanted

namespace MathlibExt.InformationTheory.ShannonSourceCodingWanted

/--
[ceil_arg_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/ShannonSourceCoding.lean)
-/
@[path]
private lemma ceil_arg_nonneg {α : Type*} [Fintype α]
  (p : α → ℝ) (hp_pos : ∀ a, 0 < p a) (hp_sum : ∑ a : α, p a = 1)
  (q : ℕ) (hq : 2 ≤ q) (a : α) :
  (0:ℝ) ≤ -Real.log (p a) / Real.log (q : ℝ) := by
  have hlogQ : (0:ℝ) < Real.log (q : ℝ) := by
    apply Real.log_pos
    exact_mod_cast lt_of_lt_of_le (by norm_num) hq
  have hlogpa : Real.log (p a) ≤ 0 :=
    Real.log_nonpos (le_of_lt (hp_pos a)) (pmf_le_one p hp_pos hp_sum a)
  exact div_nonneg (neg_nonneg.mpr hlogpa) (le_of_lt hlogQ)

end MathlibExt.InformationTheory.ShannonSourceCodingWanted

namespace MathlibExt.InformationTheory.ShannonSourceCodingWanted

/--
[ceil_inv_pow_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/ShannonSourceCoding.lean)
-/
@[path]
private lemma ceil_inv_pow_le {α : Type*}
  (p : α → ℝ) (hp_pos : ∀ a, 0 < p a)
  (q : ℕ) (hq : 2 ≤ q) (a : α) :
  (((q : ℝ) ^ (⌈-Real.log (p a) / Real.log (q : ℝ)⌉₊))⁻¹ ≤ p a) := by
  have hqpos : (0:ℝ) < (q : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num) hq
  have hlogQ : (0:ℝ) < Real.log (q : ℝ) := by
    apply Real.log_pos
    exact_mod_cast lt_of_lt_of_le (by norm_num) hq
  have hlogQne : Real.log (q : ℝ) ≠ 0 := ne_of_gt hlogQ
  have h1 : (p a)⁻¹ ≤ (q : ℝ) ^ (⌈-Real.log (p a) / Real.log (q : ℝ)⌉₊) := by
    have e1 : (p a)⁻¹ = Real.exp (-Real.log (p a)) := by
      rw [← Real.exp_log (inv_pos.mpr (hp_pos a)), Real.log_inv]
    have e2 : ((q : ℝ) ^ (⌈-Real.log (p a) / Real.log (q : ℝ)⌉₊))
      = Real.exp (((⌈-Real.log (p a) / Real.log (q : ℝ)⌉₊ : ℕ) : ℝ)
        * Real.log (q : ℝ)) := by
      rw [← Real.exp_log (pow_pos hqpos _), Real.log_pow]
    rw [e1, e2, Real.exp_le_exp]
    calc -Real.log (p a)
      = (-Real.log (p a) / Real.log (q : ℝ)) * Real.log (q : ℝ) :=
        (div_mul_cancel₀ _ hlogQne).symm
      _ ≤ (((⌈-Real.log (p a) / Real.log (q : ℝ)⌉₊ : ℕ)) : ℝ)
        * Real.log (q : ℝ) :=
        mul_le_mul_of_nonneg_right (Nat.le_ceil _) (le_of_lt hlogQ)
  have h2 := inv_anti₀ (inv_pos.mpr (hp_pos a)) h1
  rwa [inv_inv] at h2

end MathlibExt.InformationTheory.ShannonSourceCodingWanted

namespace MathlibExt.InformationTheory.ShannonSourceCodingWanted

/--
[kraft_of_ceil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/ShannonSourceCoding.lean)
-/
@[path]
private lemma kraft_of_ceil {α : Type*} [Fintype α]
  (p : α → ℝ) (hp_pos : ∀ a, 0 < p a) (hp_sum : ∑ a : α, p a = 1)
  (q : ℕ) (hq : 2 ≤ q) :
  ((∑ a : α, (((q : ℝ) ^ (⌈-Real.log (p a) / Real.log (q : ℝ)⌉₊))⁻¹)) ≤ 1) := by
  calc (∑ a : α, (((q : ℝ) ^ (⌈-Real.log (p a) / Real.log (q : ℝ)⌉₊))⁻¹))
    ≤ ∑ a : α, p a :=
      Finset.sum_le_sum (fun a _ => ceil_inv_pow_le p hp_pos q hq a)
    _ = 1 := hp_sum

end MathlibExt.InformationTheory.ShannonSourceCodingWanted

namespace MathlibExt.InformationTheory.ShannonSourceCodingWanted

/--
[expected_of_ceil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/ShannonSourceCoding.lean)
-/
@[path]
private lemma expected_of_ceil {α : Type*} [Fintype α]
  (p : α → ℝ) (hp_pos : ∀ a, 0 < p a) (hp_sum : ∑ a : α, p a = 1)
  (q : ℕ)
  (L : α → ℕ)
  (hL : ∀ a, ((L a : ℕ) : ℝ) < -Real.log (p a) / Real.log (q : ℝ) + 1) :
  (∑ a : α, p a * ((L a : ℕ) : ℝ))
    < -(∑ a : α, p a * Real.log (p a)) / Real.log (q : ℝ) + 1 := by
  have hne : (Finset.univ : Finset α).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Finset.sum_empty] at hp_sum
    norm_num at hp_sum
  have hstep : ∀ a ∈ (Finset.univ : Finset α),
    p a * ((L a : ℕ) : ℝ) < p a * (-Real.log (p a) / Real.log (q : ℝ) + 1) :=
    fun a _ => mul_lt_mul_of_pos_left (hL a) (hp_pos a)
  calc (∑ a : α, p a * ((L a : ℕ) : ℝ))
    < ∑ a : α, p a * (-Real.log (p a) / Real.log (q : ℝ) + 1) :=
      Finset.sum_lt_sum_of_nonempty hne hstep
    _ = -(∑ a : α, p a * Real.log (p a)) / Real.log (q : ℝ) + 1 := by
      calc (∑ a : α, p a * (-Real.log (p a) / Real.log (q : ℝ) + 1))
        = ∑ a : α, (-(p a * Real.log (p a)) / Real.log (q : ℝ) + p a) :=
          Finset.sum_congr rfl (fun a _ => by ring)
        _ = (∑ a : α, -(p a * Real.log (p a)) / Real.log (q : ℝ)) + ∑ a : α, p a :=
          Finset.sum_add_distrib
        _ = -(∑ a : α, p a * Real.log (p a)) / Real.log (q : ℝ) + 1 := by
          rw [← Finset.sum_div, Finset.sum_neg_distrib, hp_sum]

end MathlibExt.InformationTheory.ShannonSourceCodingWanted

namespace MathlibExt.InformationTheory.ShannonSourceCodingWanted

/--
[shannon_source_coding_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/ShannonSourceCoding.lean)
-/
@[path]
lemma shannon_source_coding_lower_bound
  [Fintype α] [Fintype β]
  {p : α → ℝ}
  {code : α → List β}
-- given
  (hp_pos : ∀ a, 0 < p a)
  (hp_sum : ∑ a : α, p a = 1)
  (hq : 2 ≤ Fintype.card β)
  (h_inj : Function.Injective code)
  (h_ud : InformationTheory.IsUniquelyDecodable (Set.range code)) :
-- imply
  -(∑ a : α, p a * Real.log (p a)) / Real.log (Fintype.card β : ℝ)
    ≤ ∑ a : α, p a * ((code a).length : ℝ) := by
-- proof
  classical
  have hcard_pos : (0:ℝ) < (Fintype.card β : ℝ) := by
    have : 0 < Fintype.card β := by omega
    exact_mod_cast this
  have hcard1 : (1:ℝ) < (Fintype.card β : ℝ) := by
    have : 1 < Fintype.card β := by omega
    exact_mod_cast this
  have hlog_pos : 0 < Real.log (Fintype.card β : ℝ) := Real.log_pos hcard1
  have hβne : Nonempty β := Fintype.card_pos_iff.mp (by omega)
  -- Kraft inequality for the finite image
  have hrange_eq : Set.range code = ↑(Finset.image code Finset.univ) := by
    ext x
    simp
  have h_ud' : InformationTheory.IsUniquelyDecodable
    (↑(Finset.image code Finset.univ) : Set (List β)) := by
    rwa [← hrange_eq]
  have hkraft0 := InformationTheory.IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one
    (S := Finset.image code Finset.univ) h_ud'
  have hInjOn : Set.InjOn code ↑(Finset.univ : Finset α) :=
    Set.injOn_of_injective h_inj
  have hkraft1 : ∑ a : α, (1 / (Fintype.card β : ℝ)) ^ (code a).length ≤ 1 := by
    have h := hkraft0
    rw [Finset.sum_image hInjOn] at h
    simpa using h
  -- Gibbs pointwise bound
  have hGibbs_sum :
    ∑ a : α, p a * Real.log (((1 / (Fintype.card β : ℝ)) ^ (code a).length) / p a) ≤ 0 := by
    have hpoint : ∀ a ∈ (Finset.univ : Finset α),
      p a * Real.log (((1 / (Fintype.card β : ℝ)) ^ (code a).length) / p a)
        ≤ (1 / (Fintype.card β : ℝ)) ^ (code a).length - p a := by
      intro a _
      have hpa : 0 < p a := hp_pos a
      have hpa_ne : p a ≠ 0 := ne_of_gt hpa
      have hr_pos : (0:ℝ) < (1 / (Fintype.card β : ℝ)) ^ (code a).length := by
        apply pow_pos
        rw [one_div]
        exact inv_pos.mpr hcard_pos
      have hr_ne : (1 / (Fintype.card β : ℝ)) ^ (code a).length ≠ 0 := ne_of_gt hr_pos
      have hdiv_pos : (0:ℝ) < ((1 / (Fintype.card β : ℝ)) ^ (code a).length) / p a :=
        div_pos hr_pos hpa
      have hlog_le := Real.log_le_sub_one_of_pos hdiv_pos
      have hmul := mul_le_mul_of_nonneg_left hlog_le (le_of_lt hpa)
      -- p * (r/p - 1) = r - p
      have heq : p a * (((1 / (Fintype.card β : ℝ)) ^ (code a).length) / p a - 1)
        = (1 / (Fintype.card β : ℝ)) ^ (code a).length - p a := by
        field_simp
      rwa [heq] at hmul
    calc ∑ a : α, p a * Real.log (((1 / (Fintype.card β : ℝ)) ^ (code a).length) / p a)
      ≤ ∑ a : α, ((1 / (Fintype.card β : ℝ)) ^ (code a).length - p a) :=
        Finset.sum_le_sum hpoint
      _ = (∑ a : α, (1 / (Fintype.card β : ℝ)) ^ (code a).length) - (∑ a : α, p a) := by
        rw [Finset.sum_sub_distrib]
      _ ≤ 0 := by
        rw [hp_sum]
        linarith [hkraft1]
  -- relate log r to length
  have hlogr : ∀ a : α, Real.log ((1 / (Fintype.card β : ℝ)) ^ (code a).length)
    = - ((code a).length : ℝ) * Real.log (Fintype.card β : ℝ) := by
    intro a
    rw [one_div, inv_pow, Real.log_inv]
    rw [Real.log_pow]
    ring
  -- expand Gibbs sum
  have hexpand : ∑ a : α, p a * Real.log (((1 / (Fintype.card β : ℝ)) ^ (code a).length) / p a)
    = -(∑ a : α, p a * ((code a).length : ℝ)) * Real.log (Fintype.card β : ℝ)
      - (∑ a : α, p a * Real.log (p a)) := by
    have hterm : ∀ a : α, p a * Real.log (((1 / (Fintype.card β : ℝ)) ^ (code a).length) / p a)
      = (p a * Real.log ((1 / (Fintype.card β : ℝ)) ^ (code a).length)
        - p a * Real.log (p a)) := by
      intro a
      have hpa_ne : p a ≠ 0 := ne_of_gt (hp_pos a)
      have hr_ne : (1 / (Fintype.card β : ℝ)) ^ (code a).length ≠ 0 := by
        apply pow_ne_zero
        rw [one_div]
        exact inv_ne_zero (ne_of_gt hcard_pos)
      rw [Real.log_div hr_ne hpa_ne]
      ring
    rw [Finset.sum_congr rfl (fun a _ => hterm a)]
    rw [Finset.sum_sub_distrib]
    congr 1
    · -- ∑ p * log r = -(∑ p * len) * log q
      have : ∀ a : α, p a * Real.log ((1 / (Fintype.card β : ℝ)) ^ (code a).length)
        = p a * ((code a).length : ℝ) * (- Real.log (Fintype.card β : ℝ)) := by
        intro a
        rw [hlogr a]
        ring
      rw [Finset.sum_congr rfl (fun a _ => this a)]
      rw [← Finset.sum_mul]
      ring
  rw [hexpand] at hGibbs_sum
  -- conclude by dividing
  rw [div_le_iff₀ hlog_pos]
  linarith

end MathlibExt.InformationTheory.ShannonSourceCodingWanted

namespace MathlibExt.InformationTheory.ShannonSourceCodingWanted

/--
[shannon_source_coding_upper_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/ShannonSourceCoding.lean)
-/
@[path]
lemma shannon_source_coding_upper_bound
  [Fintype α] [Fintype β]
  {p : α → ℝ}
-- given
  (hp_pos : ∀ a, 0 < p a)
  (hp_sum : ∑ a : α, p a = 1)
  (hq : 2 ≤ Fintype.card β) :
-- imply
  ∃ (code : α → List β),
    IsPrefixFree code ∧
    (∑ a : α, p a * ((code a).length : ℝ)) <
    -(∑ a : α, p a * Real.log (p a)) / Real.log (Fintype.card β : ℝ) + 1 := by
-- proof
  classical
  set ℓ : α → ℕ := fun a => ⌈-Real.log (p a) / Real.log (Fintype.card β : ℝ)⌉₊
    with hℓdef
  have hkraft : (∑ a : α, ((Fintype.card β : ℝ) ^ (ℓ a))⁻¹) ≤ 1 :=
    kraft_of_ceil p hp_pos hp_sum _ hq
  obtain ⟨code, hpf, hlen⟩ := (KraftMcMillan.kraft_mcmillan_lengths ℓ hq).mpr
    (by simpa [one_div] using hkraft)
  refine ⟨code, hpf, ?_⟩
  have hE : (∑ a : α, p a * ((code a).length : ℝ))
    = ∑ a : α, p a * (((ℓ a : ℕ)) : ℝ) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [hlen a]
  rw [hE]
  have hL : ∀ a, (((ℓ a : ℕ)) : ℝ)
    < -Real.log (p a) / Real.log (Fintype.card β : ℝ) + 1 := by
    intro a
    simp only [hℓdef]
    exact Nat.ceil_lt_add_one (ceil_arg_nonneg p hp_pos hp_sum _ hq a)
  exact expected_of_ceil p hp_pos hp_sum _ ℓ hL
end MathlibExt.InformationTheory.ShannonSourceCodingWanted



-- created on 2026-10-20
-- updated on 2026-10-26
