module

public import Mathlib
public import Theorem.Analysis.Section_5_3.Part12
public import Abbrev.Analysis.Section_5_4.Part2
public import Theorem.Analysis.Section_5_4
public import Theorem.Analysis.Section_5_3.Part9

public section
/-!
# Analysis I, Section 5.4: Ordering the reals

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordering on the real line

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

/-- Constant sequences are Cauchy. Private helper only (via `Sequence.IsCauchy.coe`). -/
private theorem isCauchy_ofNatFun_const (q : ℚ) :
    (Sequence.ofNatFun (fun _ ↦ q)).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  intro ε hε
  refine ⟨0, ?_⟩
  intro j _ k _
  rw [Section_4_3.dist_eq]
  simpa using le_of_lt hε

private theorem eventually_le_of_eventuallyClose_zero {a : ℕ → ℚ} {ε : ℚ}
    (h : ε.EventuallyClose (Sequence.ofNatFun a) (Sequence.ofNatFun (fun _ ↦ (0:ℚ)))) :
    ∃ N : ℕ, ∀ n ≥ N, |a n| ≤ ε := by
  obtain ⟨N, hN⟩ := h
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
  have hc : (n : ℤ) ≥ ((Sequence.ofNatFun (fun _ ↦ (0:ℚ))).from N).n₀ := by
    rw [from_n₀, ofNatFun_n₀]; simpa using hnZ
  have hclose := hN n hb hc
  have hn0 : 0 ≤ (n : ℤ) := Int.natCast_nonneg n
  rw [from_seq _ (by rw [ofNatFun_n₀]; simpa using hnZ),
      from_seq (Sequence.ofNatFun (fun _ ↦ (0:ℚ))) (by rw [ofNatFun_n₀]; simpa using hnZ),
      ofNatFun_seq_of_nonneg a hn0,
      ofNatFun_seq_of_nonneg (fun _ ↦ (0:ℚ)) hn0,
      Int.toNat_natCast, Section_4_3.close_iff, sub_zero] at hclose
  exact hclose

private theorem eventually_le_of_eventuallyClose {a b : ℕ → ℚ} {ε : ℚ}
    (h : ε.EventuallyClose (Sequence.ofNatFun a) (Sequence.ofNatFun b)) :
    ∃ N : ℕ, ∀ n ≥ N, |a n - b n| ≤ ε := by
  obtain ⟨N, hN⟩ := h
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

private theorem lim_ne_zero_of_boundedAwayZero {a : ℕ → ℚ}
    (ha : BoundedAwayZero a) (hc : (Sequence.ofNatFun a).IsCauchy) :
    LIM a ≠ 0 := by
  intro h0
  rw [← Real.LIM.zero] at h0
  have heq : Sequence.Equiv a (fun _ ↦ (0:ℚ)) :=
    (Real.LIM_eq_LIM hc (isCauchy_ofNatFun_const 0)).mp h0
  rw [bounded_away_zero_def] at ha
  obtain ⟨c, hcpos, hbound⟩ := ha
  obtain ⟨N, hN⟩ := eventually_le_of_eventuallyClose_zero (heq (c / 2) (half_pos hcpos))
  have hge : |a N| ≥ c := hbound N
  have hle : |a N| ≤ c / 2 := hN N le_rfl
  linarith

public theorem Real.isPos_def (x:Real) :
    IsPos x ↔ ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (Sequence.ofNatFun a).IsCauchy ∧ x = LIM a := by rfl

public theorem Real.isNeg_def (x:Real) :
    IsNeg x ↔ ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (Sequence.ofNatFun a).IsCauchy ∧ x = LIM a := by rfl

public theorem Real.not_zero_pos (x:Real) : ¬(x = 0 ∧ x.IsPos) := by
  rintro ⟨rfl, hxpos⟩
  rw [isPos_def] at hxpos
  obtain ⟨a, hpos, hcauchy, hlim⟩ := hxpos
  exact (lim_ne_zero_of_boundedAwayZero (BoundedAwayZero.boundedAwayPos hpos) hcauchy) hlim.symm

public theorem Real.nonzero_of_pos {x:Real} (hx: x.IsPos) : x ≠ 0 := by
  have := not_zero_pos x
  simpa [hx] using this

public theorem Real.not_zero_neg (x:Real) : ¬(x = 0 ∧ x.IsNeg) := by
  rintro ⟨rfl, hxneg⟩
  rw [isNeg_def] at hxneg
  obtain ⟨a, hneg, hcauchy, hlim⟩ := hxneg
  exact (lim_ne_zero_of_boundedAwayZero (BoundedAwayZero.boundedAwayNeg hneg) hcauchy) hlim.symm

public theorem Real.nonzero_of_neg {x:Real} (hx: x.IsNeg) : x ≠ 0 := by
  have := not_zero_neg x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
public theorem Real.not_pos_neg (x:Real) : ¬(x.IsPos ∧ x.IsNeg) := by
  rintro ⟨hpos, hneg⟩
  rw [isPos_def] at hpos
  rw [isNeg_def] at hneg
  obtain ⟨a, hapos, hacauchy, halim⟩ := hpos
  obtain ⟨b, hbneg, hbcauchy, hblim⟩ := hneg
  have heq : Sequence.Equiv a b :=
    (Real.LIM_eq_LIM hacauchy hbcauchy).mp (halim.symm.trans hblim)
  obtain ⟨c, hcpos, ha⟩ := hapos
  obtain ⟨d, hdpos, hb⟩ := hbneg
  have hgap (n : ℕ) : |a n - b n| ≥ c + d := by
    have hsub : a n - b n ≥ c + d := by linarith [ha n, hb n]
    have hnn : 0 ≤ a n - b n := by linarith
    rwa [abs_of_nonneg hnn]
  have hε : (c + d) / 2 > 0 := by positivity
  obtain ⟨N, hN⟩ := eventually_le_of_eventuallyClose (heq ((c + d) / 2) hε)
  have hle : |a N - b N| ≤ (c + d) / 2 := hN N le_rfl
  have hge : |a N - b N| ≥ c + d := hgap N
  linarith

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
public theorem Real.neg_iff_pos_of_neg (x:Real) : x.IsNeg ↔ (-x).IsPos := by
  constructor
  · intro hx
    rw [isNeg_def] at hx
    obtain ⟨a, hneg, hcauchy, rfl⟩ := hx
    rw [isPos_def]
    refine ⟨-a, ?_, Sequence.IsCauchy.neg a hcauchy, neg_LIM a hcauchy⟩
    obtain ⟨c, hc, ha⟩ := hneg
    refine ⟨c, hc, ?_⟩
    intro n
    have := ha n
    simp [Pi.neg_apply]
    linarith
  · intro hx
    rw [isPos_def] at hx
    obtain ⟨a, hpos, hcauchy, hxeq⟩ := hx
    rw [isNeg_def]
    have hx' : x = LIM (-a) := by
      have : -x = LIM a := hxeq
      rw [← neg_LIM a hcauchy, ← this, neg_neg]
    refine ⟨-a, ?_, Sequence.IsCauchy.neg a hcauchy, hx'⟩
    obtain ⟨c, hc, ha⟩ := hpos
    refine ⟨c, hc, ?_⟩
    intro n
    have := ha n
    simp [Pi.neg_apply]
    linarith

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
public theorem Real.pos_add {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x+y).IsPos := by
  rw [isPos_def] at hx hy ⊢
  obtain ⟨a, ha, hca, rfl⟩ := hx
  obtain ⟨b, hb, hcb, rfl⟩ := hy
  refine ⟨a+b, ?_, Sequence.IsCauchy.add hca hcb, LIM_add hca hcb⟩
  obtain ⟨c, hc, ha'⟩ := ha
  obtain ⟨d, hd, hb'⟩ := hb
  refine ⟨c+d, by positivity, ?_⟩
  intro n
  simp [Pi.add_apply]
  linarith [ha' n, hb' n]

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
public theorem Real.pos_mul {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x*y).IsPos := by
  rw [isPos_def] at hx hy ⊢
  obtain ⟨a, ha, hca, rfl⟩ := hx
  obtain ⟨b, hb, hcb, rfl⟩ := hy
  refine ⟨a*b, ?_, Sequence.IsCauchy.mul hca hcb, LIM_mul hca hcb⟩
  obtain ⟨c, hc, ha'⟩ := ha
  obtain ⟨d, hd, hb'⟩ := hb
  refine ⟨c*d, by positivity, ?_⟩
  intro n
  simp [Pi.mul_apply]
  have han : c ≤ a n := ha' n
  have hbn : d ≤ b n := hb' n
  have ha0 : 0 ≤ a n := le_trans (le_of_lt hc) han
  have hb0 : 0 ≤ b n := le_trans (le_of_lt hd) hbn
  nlinarith

public theorem Real.pos_of_coe (q:ℚ) : (q:Real).IsPos ↔ q > 0 := by
  constructor
  · intro h
    rw [isPos_def] at h
    obtain ⟨a, hpos, hca, hlim⟩ := h
    obtain ⟨c, hc, ha⟩ := hpos
    have hq : LIM (fun _ ↦ q) = LIM a := by rw [← ratCast_def, hlim]
    have heq : Sequence.Equiv (fun _ ↦ q) a :=
      (LIM_eq_LIM (Sequence.IsCauchy.const q) hca).mp hq
    obtain ⟨N, hN⟩ := eventually_le_of_eventuallyClose (heq (c / 2) (half_pos hc))
    have hle : |q - a N| ≤ c / 2 := hN N le_rfl
    have hge : a N ≥ c := ha N
    have : q ≥ c / 2 := by
      have : -(c / 2) ≤ q - a N := (abs_le.mp hle).1
      linarith
    linarith
  · intro hq
    rw [isPos_def]
    refine ⟨fun _ ↦ q, ⟨q, hq, fun _ => le_rfl⟩, Sequence.IsCauchy.const q, ratCast_def q⟩

public theorem Real.neg_of_coe (q:ℚ) : (q:Real).IsNeg ↔ q < 0 := by
  rw [neg_iff_pos_of_neg, neg_ratCast, pos_of_coe]
  constructor <;> intro h <;> linarith

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
public theorem Real.trichotomous (x:Real) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  obtain ⟨a0, ha0, rfl⟩ := eq_lim x
  by_cases hx : LIM a0 = 0
  · exact Or.inl hx
  obtain ⟨b, hb, hbaz, hlim⟩ := boundedAwayZero_of_nonzero hx
  rw [hlim]
  rw [bounded_away_zero_def] at hbaz
  obtain ⟨c, hcpos, hbound⟩ := hbaz
  obtain ⟨N, hN⟩ := (Sequence.IsCauchy.coe b).mp hb (c / 2) (half_pos hcpos)
  have hBN : |b N| ≥ c := hbound N
  by_cases hsign : 0 ≤ b N
  · right; left
    have hbN : b N ≥ c := by
      have : |b N| = b N := abs_of_nonneg hsign
      linarith
    have how : ∀ j ≥ N, b j ≥ c / 2 := by
      intro j hj
      have hdist := hN j hj N le_rfl
      rw [Section_4_3.dist_eq] at hdist
      have : b N - c / 2 ≤ b j := by
        have := (abs_le.mp hdist).1
        linarith
      linarith
    set a' : ℕ → ℚ := fun n ↦ if n < N then c / 2 else b n
    have hequiv : Sequence.Equiv a' b := by
      intro ε' hε'
      refine ⟨(N:ℤ), ?_⟩
      intro n hnA hnB
      have hfrom0 : ((Sequence.ofNatFun a').from (N:ℤ)).n₀ = (N:ℤ) := by
        rw [from_n₀, ofNatFun_n₀]; simp
      have npos : 0 ≤ n := by rw [hfrom0] at hnA; linarith
      have hnN : (N:ℤ) ≤ n := by rwa [hfrom0] at hnA
      lift n to ℕ using npos
      have hab : a' n = b n := if_neg (not_lt.mpr (by exact_mod_cast hnN))
      have seq_from_a : ((Sequence.ofNatFun a').from (N:ℤ)).seq n = a' n := by
        have hbnd : ((Sequence.ofNatFun a').from (N:ℤ)).n₀ ≤ (n:ℤ) := by rwa [hfrom0]
        rw [from_seq _ (by rw [ofNatFun_n₀]; simpa using hnN), ofNatFun_seq_of_nonneg a' (Int.natCast_nonneg n),
            Int.toNat_natCast]
      have seq_from_b : ((Sequence.ofNatFun b).from (N:ℤ)).seq n = b n := by
        rw [from_seq (Sequence.ofNatFun b) (by rw [ofNatFun_n₀]; simpa using hnN),
            ofNatFun_seq_of_nonneg b (Int.natCast_nonneg n), Int.toNat_natCast]
      rw [seq_from_a, seq_from_b, hab, Section_4_3.close_iff, sub_self, abs_zero]
      exact le_of_lt hε'
    have ha' : (Sequence.ofNatFun a').IsCauchy := by
      rw [Sequence.IsCauchy.coe] at hb ⊢
      intro ε' hε'
      obtain ⟨M, hM⟩ := hb ε' hε'
      refine ⟨max M N, ?_⟩
      intro j hj k hk
      have hjn : N ≤ j := le_trans (le_max_right M N) hj
      have hkn : N ≤ k := le_trans (le_max_right M N) hk
      have hjM : M ≤ j := le_trans (le_max_left M N) hj
      have hkM : M ≤ k := le_trans (le_max_left M N) hk
      have aj : a' j = b j := if_neg (not_lt.mpr hjn)
      have ak : a' k = b k := if_neg (not_lt.mpr hkn)
      rw [aj, ak]
      exact hM j hjM k hkM
    rw [isPos_def]
    refine ⟨a', ?_, ha', ((LIM_eq_LIM ha' hb).mpr hequiv).symm⟩
    refine ⟨c / 2, half_pos hcpos, ?_⟩
    intro n
    by_cases hn : n < N
    · simp [a', hn]
    · simp [a', hn]
      exact how n (le_of_not_gt hn)
  · right; right
    have hbN : b N ≤ -c := by
      have : |b N| = -b N := abs_of_neg (lt_of_not_ge hsign)
      linarith
    have how : ∀ j ≥ N, b j ≤ -(c / 2) := by
      intro j hj
      have hdist := hN j hj N le_rfl
      rw [Section_4_3.dist_eq] at hdist
      have : b j ≤ b N + c / 2 := by
        have := (abs_le.mp hdist).2
        linarith
      linarith
    set a' : ℕ → ℚ := fun n ↦ if n < N then -(c / 2) else b n
    have hequiv : Sequence.Equiv a' b := by
      intro ε' hε'
      refine ⟨(N:ℤ), ?_⟩
      intro n hnA hnB
      have hfrom0 : ((Sequence.ofNatFun a').from (N:ℤ)).n₀ = (N:ℤ) := by
        rw [from_n₀, ofNatFun_n₀]; simp
      have npos : 0 ≤ n := by rw [hfrom0] at hnA; linarith
      have hnN : (N:ℤ) ≤ n := by rwa [hfrom0] at hnA
      lift n to ℕ using npos
      have hab : a' n = b n := if_neg (not_lt.mpr (by exact_mod_cast hnN))
      have seq_from_a : ((Sequence.ofNatFun a').from (N:ℤ)).seq n = a' n := by
        rw [from_seq _ (by rw [ofNatFun_n₀]; simpa using hnN), ofNatFun_seq_of_nonneg a' (Int.natCast_nonneg n),
            Int.toNat_natCast]
      have seq_from_b : ((Sequence.ofNatFun b).from (N:ℤ)).seq n = b n := by
        rw [from_seq (Sequence.ofNatFun b) (by rw [ofNatFun_n₀]; simpa using hnN),
            ofNatFun_seq_of_nonneg b (Int.natCast_nonneg n), Int.toNat_natCast]
      rw [seq_from_a, seq_from_b, hab, Section_4_3.close_iff, sub_self, abs_zero]
      exact le_of_lt hε'
    have ha' : (Sequence.ofNatFun a').IsCauchy := by
      rw [Sequence.IsCauchy.coe] at hb ⊢
      intro ε' hε'
      obtain ⟨M, hM⟩ := hb ε' hε'
      refine ⟨max M N, ?_⟩
      intro j hj k hk
      have hjn : N ≤ j := le_trans (le_max_right M N) hj
      have hkn : N ≤ k := le_trans (le_max_right M N) hk
      have hjM : M ≤ j := le_trans (le_max_left M N) hj
      have hkM : M ≤ k := le_trans (le_max_left M N) hk
      have aj : a' j = b j := if_neg (not_lt.mpr hjn)
      have ak : a' k = b k := if_neg (not_lt.mpr hkn)
      rw [aj, ak]
      exact hM j hjM k hkM
    rw [isNeg_def]
    refine ⟨a', ?_, ha', ((LIM_eq_LIM ha' hb).mpr hequiv).symm⟩
    refine ⟨c / 2, half_pos hcpos, ?_⟩
    intro n
    by_cases hn : n < N
    · simp [a', hn]
    · simp [a', hn]
      exact how n (le_of_not_gt hn)

public theorem Real.mul_pos_neg {x y:Real} (hx: x.IsPos) (hy: y.IsNeg) : (x * y).IsNeg := by
  rw [isPos_def] at hx
  rw [isNeg_def] at hy ⊢
  obtain ⟨a, ha, hca, rfl⟩ := hx
  obtain ⟨b, hb, hcb, rfl⟩ := hy
  refine ⟨a*b, ?_, Sequence.IsCauchy.mul hca hcb, LIM_mul hca hcb⟩
  obtain ⟨c, hc, ha'⟩ := ha
  obtain ⟨d, hd, hb'⟩ := hb
  refine ⟨c*d, by positivity, ?_⟩
  intro n
  simp [Pi.mul_apply]
  have han : c ≤ a n := ha' n
  have hbn : b n ≤ -d := hb' n
  have ha0 : 0 ≤ a n := le_trans (le_of_lt hc) han
  have : a n * b n ≤ a n * (-d) := mul_le_mul_of_nonneg_left hbn ha0
  have : a n * (-d) ≤ c * (-d) := by
    have : -d ≤ 0 := by linarith
    exact mul_le_mul_of_nonpos_right han this
  have : c * (-d) = -(c * d) := by ring
  linarith


end Chapter5
