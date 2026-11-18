module

public import Mathlib
public import Theorem.Analysis.Section_5_2.Part2
public import Mathlib.Algebra.Group.MinimalAxioms
public import Abbrev.Analysis.Section_5_3.Part3

public section
/-!
# Analysis I, Section 5.3: The construction of the real numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a formal limit of a Cauchy sequence.
- Construction of a real number type `Chapter5.Real`.
- Basic arithmetic operations and properties.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


namespace Chapter5

private theorem ofNatFun_n₀ (a : ℕ → ℚ) : (Sequence.ofNatFun a).n₀ = 0 := rfl

private theorem from_n₀ (a : Sequence) (n₁ : ℤ) :
    (a.from n₁).n₀ = max a.n₀ n₁ := rfl

private theorem from_seq (a : Sequence) {n₁ n : ℤ} (h : n ≥ max a.n₀ n₁) :
    (a.from n₁).seq n = a.seq n := by
  dsimp [Sequence.from, Sequence.mk']
  split
  · rfl
  · omega

private theorem ofNatFun_seq_of_nonneg (a : ℕ → ℚ) {n : ℤ} (hn : 0 ≤ n) :
    (Sequence.ofNatFun a).seq n = a n.toNat := by
  simp [Sequence.ofNatFun, hn]

/-- Constant sequences are Cauchy. Private helper only. -/
private theorem isCauchy_ofNatFun_const (q : ℚ) :
    (Sequence.ofNatFun (fun _ ↦ q)).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  intro ε hε
  refine ⟨0, ?_⟩
  intro j _ k _
  rw [Section_4_3.dist_eq]
  simpa using le_of_lt hε

private theorem eventuallyClose_iff {a b : ℕ → ℚ} {ε : ℚ} :
    ε.EventuallyClose (Sequence.ofNatFun a) (Sequence.ofNatFun b) ↔
      ∃ N : ℕ, ∀ n ≥ N, |a n - b n| ≤ ε := by
  constructor
  · intro ⟨N, hN⟩
    set N' : ℕ := Int.toNat (max N 0)
    refine ⟨N', ?_⟩
    intro n hn
    have hN0 : 0 ≤ max N 0 := le_max_right _ _
    have hnZ : (n : ℤ) ≥ max N 0 := by
      have hcast : (N' : ℤ) = max N 0 := Int.toNat_of_nonneg hN0
      have : (N' : ℤ) ≤ (n : ℤ) := Int.ofNat_le.mpr hn
      linarith
    have hb : (n : ℤ) ≥ ((Sequence.ofNatFun a).from N).n₀ := by
      rw [from_n₀, ofNatFun_n₀]; simpa using hnZ
    have hc : (n : ℤ) ≥ ((Sequence.ofNatFun b).from N).n₀ := by
      rw [from_n₀, ofNatFun_n₀]; simpa using hnZ
    have hclose := hN n hb hc
    have hn0 : 0 ≤ (n : ℤ) := Int.natCast_nonneg n
    rw [from_seq _ (by rw [ofNatFun_n₀]; simpa using hnZ),
        from_seq (Sequence.ofNatFun b) (by rw [ofNatFun_n₀]; simpa using hnZ),
        ofNatFun_seq_of_nonneg a hn0, ofNatFun_seq_of_nonneg b hn0,
        Int.toNat_natCast, Section_4_3.close_iff] at hclose
    exact hclose
  · intro ⟨N, hN⟩
    refine ⟨(N : ℤ), ?_⟩
    intro n hnA hnB
    have hn0N : 0 ≤ n ∧ (N : ℤ) ≤ n := by
      rw [from_n₀, ofNatFun_n₀] at hnA
      constructor <;> omega
    have hmax : n ≥ max (Sequence.ofNatFun a).n₀ (N : ℤ) := by
      rw [ofNatFun_n₀]; omega
    have hmaxb : n ≥ max (Sequence.ofNatFun b).n₀ (N : ℤ) := by
      rw [ofNatFun_n₀]; omega
    have hnNat : N ≤ n.toNat := by
      have : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0N.1
      exact Nat.cast_le.mp (this ▸ hn0N.2)
    rw [from_seq _ hmax, from_seq (Sequence.ofNatFun b) hmaxb,
        ofNatFun_seq_of_nonneg a hn0N.1, ofNatFun_seq_of_nonneg b hn0N.1,
        Section_4_3.close_iff]
    exact hN n.toNat hnNat

public theorem bounded_away_zero_def (a:ℕ → ℚ) : BoundedAwayZero a ↔
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c := by rfl

/-- If a real is nonzero, it is the limit of a Cauchy sequence bounded away from zero. -/
public theorem Real.boundedAwayZero_of_nonzero {x:Real} (hx: x ≠ 0) :
    ∃ a:ℕ → ℚ, (Sequence.ofNatFun a).IsCauchy ∧ BoundedAwayZero a ∧ x = LIM a := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨b, hb, rfl⟩ := eq_lim x
  have hx0 : LIM b ≠ LIM (fun _ ↦ (0:ℚ)) := by
    simpa [LIM.zero] using hx
  have hneq : ¬ Sequence.Equiv b (fun _ ↦ (0:ℚ)) := by
    rwa [← LIM_eq_LIM hb (isCauchy_ofNatFun_const 0)]
  rw [Sequence.equiv_def] at hneq
  obtain ⟨ε, hεcl⟩ := not_forall.mp hneq
  obtain ⟨hε, hnotClose⟩ := not_imp.mp hεcl
  have hnot : ¬ ∃ N : ℕ, ∀ n ≥ N, |b n - (0:ℚ)| ≤ ε := by
    rwa [← eventuallyClose_iff]
  have hxN : ∀ N : ℕ, ∃ n ≥ N, ¬ |b n - (0:ℚ)| ≤ ε := by
    intro N
    have hN := not_exists.mp hnot N
    obtain ⟨n, hn⟩ := not_forall.mp hN
    obtain ⟨hnN, hnε⟩ := not_imp.mp hn
    exact ⟨n, hnN, hnε⟩
  obtain ⟨N, hbN⟩ := (Sequence.IsCauchy.coe b).mp hb (ε / 2) (half_pos hε)
  obtain ⟨n₀, hn₀, hx'⟩ := hxN N
  have hgt : ε < |b n₀| := by
    have : ε < |b n₀ - 0| := lt_of_not_ge hx'
    simpa using this
  have how : ∀ j ≥ N, |b j| ≥ ε / 2 := by
    intro j hj
    have hdist := hbN j hj n₀ hn₀
    rw [Section_4_3.dist_eq] at hdist
    have : |b n₀| ≤ |b j| + |b j - b n₀| := by
      calc
        |b n₀| = |b j + (b n₀ - b j)| := by ring
        _ ≤ |b j| + |b n₀ - b j| := abs_add_le _ _
        _ = |b j| + |b j - b n₀| := by rw [abs_sub_comm]
    linarith
  set a : ℕ → ℚ := fun n ↦ if n < n₀ then ε / 2 else b n
  have not_hard : Sequence.Equiv a b := by
    rw [Sequence.equiv_def]
    intro ε' hε'
    rw [eventuallyClose_iff]
    refine ⟨n₀, ?_⟩
    intro n hn
    have : a n = b n := if_neg (not_lt.mpr hn)
    simp [this]
    exact le_of_lt hε'
  have ha : (Sequence.ofNatFun a).IsCauchy := by
    rw [Sequence.IsCauchy.coe] at hb ⊢
    intro ε' hε'
    obtain ⟨M, hM⟩ := hb ε' hε'
    refine ⟨max M n₀, ?_⟩
    intro j hj k hk
    have hjn : n₀ ≤ j := le_trans (le_max_right M n₀) hj
    have hkn : n₀ ≤ k := le_trans (le_max_right M n₀) hk
    have hjM : M ≤ j := le_trans (le_max_left M n₀) hj
    have hkM : M ≤ k := le_trans (le_max_left M n₀) hk
    have aj : a j = b j := if_neg (not_lt.mpr hjn)
    have ak : a k = b k := if_neg (not_lt.mpr hkn)
    rw [aj, ak]
    exact hM j hjM k hkM
  refine ⟨a, ha, ?_, ((LIM_eq_LIM ha hb).mpr not_hard).symm⟩
  rw [bounded_away_zero_def]
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro n
  by_cases hn : n < n₀
  · simp [a, hn]
    exact le_abs_self _
  · simp [a, hn]
    have : N ≤ n := le_trans hn₀ (le_of_not_gt hn)
    exact how n this

public theorem Real.nonzero_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a) (n: ℕ) :
    a n ≠ 0 := by
  choose c hc ha using ha; specialize ha n; contrapose! ha; simp [ha, hc]

/-- Lemma 5.3.15 -/
public theorem Real.inv_isCauchy_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
    (ha_cauchy: (Sequence.ofNatFun a).IsCauchy) :
    (Sequence.ofNatFun (a⁻¹)).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  have ha' (n:ℕ) : a n ≠ 0 := nonzero_of_boundedAwayZero ha n
  rw [bounded_away_zero_def] at ha; choose c hc ha using ha
  simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at ha_cauchy ⊢
  intro ε hε; specialize ha_cauchy (c^2 * ε) (by positivity)
  choose N ha_cauchy using ha_cauchy; use N;
  peel 4 ha_cauchy with n hn m hm ha_cauchy
  calc
    _ = |(a m - a n) / (a m * a n)| := by
        congr; simp only [Pi.inv_apply]; field_simp [ha' m, ha' n]
    _ ≤ |a m - a n| / c^2 := by rw [abs_div, abs_mul, sq]; gcongr <;> solve_by_elim
    _ = |a n - a m| / c^2 := by rw [abs_sub_comm]
    _ ≤ (c^2 * ε) / c^2 := by gcongr
    _ = ε := by field_simp [hc]

/-- Lemma 5.3.17 (Reciprocation is well-defined) -/
public theorem Real.inv_of_equiv {a b:ℕ → ℚ} (ha: BoundedAwayZero a)
    (ha_cauchy: (Sequence.ofNatFun a).IsCauchy) (hb: BoundedAwayZero b)
    (hb_cauchy: (Sequence.ofNatFun b).IsCauchy) (hlim: LIM a = LIM b) :
    LIM a⁻¹ = LIM b⁻¹ := by
  -- This proof is written to follow the structure of the original text.
  set P := LIM a⁻¹ * LIM a * LIM b⁻¹
  have hainv_cauchy := Real.inv_isCauchy_of_boundedAwayZero ha ha_cauchy
  have hbinv_cauchy := Real.inv_isCauchy_of_boundedAwayZero hb hb_cauchy
  have haainv_cauchy := hainv_cauchy.mul ha_cauchy
  have habinv_cauchy := hainv_cauchy.mul hb_cauchy
  have claim1 : P = LIM b⁻¹ := by
    simp only [P, LIM_mul hainv_cauchy ha_cauchy, LIM_mul haainv_cauchy hbinv_cauchy]
    rcongr n; simp [nonzero_of_boundedAwayZero ha n]
  have claim2 : P = LIM a⁻¹ := by
    simp only [P, hlim, LIM_mul hainv_cauchy hb_cauchy, LIM_mul habinv_cauchy hbinv_cauchy]
    rcongr n; simp [nonzero_of_boundedAwayZero hb n]
  grind

end Chapter5
