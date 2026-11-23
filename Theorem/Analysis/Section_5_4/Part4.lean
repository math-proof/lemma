module

public import Mathlib
public import Theorem.Analysis.Section_5_3.Part12
public import Instance.Analysis.Section_5_4
public import Theorem.Analysis.Section_5_4.Part2
public import Theorem.Analysis.Section_5_3.Part9
public import Theorem.Analysis.Section_5_3.Part11
public import Theorem.Analysis.Section_5_3.Part4
public import Theorem.Analysis.Section_5_3.Part7
public import Theorem.Analysis.Section_5_1.Part8

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

public section


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

/-- Distributivity law used here; `Real.instCommRing` (Instance-owned, still missing) is the
    historical home of `left_distrib`. Private only — do not publish a near-hit name. -/
private theorem mul_sub_right (x y z : Real) : (x - y) * z = x * z - y * z := by
  obtain ⟨A, hA, rfl⟩ := Real.eq_lim x
  obtain ⟨B, hB, rfl⟩ := Real.eq_lim y
  obtain ⟨C, hC, rfl⟩ := Real.eq_lim z
  have hsub := Sequence.IsCauchy.sub hA hB
  have hAC := Sequence.IsCauchy.mul hA hC
  have hBC := Sequence.IsCauchy.mul hB hC
  rw [Real.LIM_sub hA hB, Real.LIM_mul hsub hC, Real.LIM_mul hA hC, Real.LIM_mul hB hC, Real.LIM_sub hAC hBC]
  have hfun : (A - B) * C = A * C - B * C := by
    ext n
    simp [Pi.sub_apply, Pi.mul_apply]
    ring
  rw [hfun]

private theorem zero_eq_ratCast : (0:Real) = ((0:ℚ):Real) := rfl

private theorem one_eq_ratCast : (1:Real) = ((1:ℚ):Real) := rfl

private theorem zero_mul_real (x : Real) : (0:Real) * x = 0 := by
  obtain ⟨A, hA, rfl⟩ := Real.eq_lim x
  have h0c := Sequence.IsCauchy.const (0:ℚ)
  rw [zero_eq_ratCast, Real.ratCast_def, Real.LIM_mul h0c hA]
  have hfun : (fun _ ↦ (0:ℚ)) * A = fun _ ↦ (0:ℚ) := by
    ext n
    simp [Pi.mul_apply]
  rw [hfun, ← Real.ratCast_def, ← zero_eq_ratCast]

private theorem nat_one_mul (x : Real) : ((1:ℕ):Real) * x = x := by
  change ((1:ℚ):Real) * x = x
  exact Real.one_mul x

private theorem real_sub_add (x y z : Real) : (x - y) + (y - z) = x - z := by
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
  rw [add_assoc x (-y) (y + -z)]
  rw [← add_assoc (-y) y (-z)]
  rw [neg_add_cancel, zero_add]

theorem Real.lt_iff (x y:Real) : x < y ↔ (x-y).IsNeg := by rfl

/-- Private transitivity of `<`. No `Preorder`/`PartialOrder` instance exists yet. -/
private theorem real_lt_trans {x y z : Real} (hxy : x < y) (hyz : y < z) : x < z := by
  have h1 : (y - x).IsPos := by
    rw [← neg_sub x y]
    exact (Real.neg_iff_pos_of_neg (x - y)).mp ((Real.lt_iff x y).mp hxy)
  have h2 : (z - y).IsPos := by
    rw [← neg_sub y z]
    exact (Real.neg_iff_pos_of_neg (y - z)).mp ((Real.lt_iff y z).mp hyz)
  have hzxim : (z - x).IsPos := by
    rw [← real_sub_add z y x]
    exact Real.pos_add h2 h1
  have : (x - z).IsNeg :=
    (Real.neg_iff_pos_of_neg (x - z)).mpr (by rwa [neg_sub])
  exact (Real.lt_iff x z).mpr this

theorem Real.le_iff (x y:Real) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Real.gt_iff (x y:Real) : x > y ↔ (x-y).IsPos := by
  have h : y < x ↔ (y-x).IsNeg := lt_iff y x
  have h' : (y-x).IsNeg ↔ (x-y).IsPos := by
    rw [neg_iff_pos_of_neg, neg_sub]
  simpa [gt_iff_lt] using h.trans h'

theorem Real.lt_of_coe (q q':ℚ): q < q' ↔ (q:Real) < (q':Real) := by
  rw [lt_iff, ratCast_sub, neg_of_coe]
  constructor <;> intro h <;> linarith

theorem Real.gt_of_coe (q q':ℚ): q > q' ↔ (q:Real) > (q':Real) := Real.lt_of_coe _ _

theorem Real.isNeg_iff (x:Real) : x.IsNeg ↔ x < 0 := by
  rw [lt_iff, sub_zero]

theorem Real.isPos_iff (x:Real) : x.IsPos ↔ x > 0 := by
  rw [gt_iff, sub_zero]

theorem Real.antisymm (x y:Real) : x < y ↔ y > x := Iff.rfl

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_lt_mul_right {x y z:Real} (hxy: x < y) (hz: z.IsPos) : x * z < y * z := by
  rw [antisymm, gt_iff] at hxy ⊢
  convert pos_mul hxy hz using 1
  exact (mul_sub_right y x z).symm

theorem Real.mul_le_mul_left {x y z:Real} (hxy: x ≤ y) (hz: z.IsPos) : z * x ≤ z * y := by
  rw [le_iff] at hxy ⊢
  rcases hxy with hlt | rfl
  · left
    have := mul_lt_mul_right hlt hz
    simpa [mul_comm z x, mul_comm z y] using this
  · right; rfl

/-- Proposition 5.4.8 -/
theorem Real.inv_of_pos {x:Real} (hx: x.IsPos) : x⁻¹.IsPos := by
  have hnon: x ≠ 0 := nonzero_of_pos hx
  have hident : x⁻¹ * x = 1 := inv_mul_self hnon
  have hinv_non: x⁻¹ ≠ 0 := by
    intro h0
    have h01 : (0:Real) = (1:Real) := by
      have := hident
      rw [h0, zero_mul_real] at this
      exact this
    have hone : (1:Real).IsPos := (pos_of_coe 1).mpr (by norm_num)
    exact (not_zero_pos (1:Real)) ⟨h01.symm, hone⟩
  have hnonneg : ¬x⁻¹.IsNeg := by
    intro h
    have hneg : (x * x⁻¹).IsNeg := mul_pos_neg hx h
    rw [self_mul_inv hnon] at hneg
    rw [neg_iff_pos_of_neg] at hneg
    rw [one_eq_ratCast, neg_ratCast, pos_of_coe] at hneg
    linarith
  have trich := trichotomous x⁻¹
  simpa [hinv_non, hnonneg] using trich

theorem Real.div_of_pos {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x/y).IsPos := by
  rw [div_eq]
  exact pos_mul hx (inv_of_pos hy)

theorem Real.inv_of_gt {x y:Real} (hx: x.IsPos) (hy: y.IsPos) (hxy: x > y) : x⁻¹ < y⁻¹ := by
  have hxnon: x ≠ 0 := nonzero_of_pos hx
  have hynon: y ≠ 0 := nonzero_of_pos hy
  have hxinv : x⁻¹.IsPos := inv_of_pos hx
  have hyinv : y⁻¹.IsPos := inv_of_pos hy
  have h1 : y * x⁻¹ < x * x⁻¹ := mul_lt_mul_right hxy hxinv
  rw [self_mul_inv hxnon] at h1
  have h2 : (y * x⁻¹) * y⁻¹ < (1:Real) * y⁻¹ := mul_lt_mul_right h1 hyinv
  have hleft : (y * x⁻¹) * y⁻¹ = x⁻¹ := by
    rw [mul_assoc, mul_comm x⁻¹, ← mul_assoc, self_mul_inv hynon]
    exact Real.one_mul _
  have hright : (1:Real) * y⁻¹ = y⁻¹ := Real.one_mul _
  rw [hleft, hright] at h2
  exact h2

/-- Proposition 5.4.9 (The non-negative reals are closed) -/
theorem Real.LIM_of_nonneg {a: ℕ → ℚ} (ha: ∀ n, a n ≥ 0) (hcauchy: (Sequence.ofNatFun a).IsCauchy) :
    LIM a ≥ 0 := by
  by_contra hlim
  set x := LIM a
  change ¬(0 ≤ x) at hlim
  rw [le_iff, not_or] at hlim
  obtain ⟨hnlt, hne⟩ := hlim
  have hxneg : x.IsNeg := by
    rcases trichotomous x with h0 | hp | hn
    · exact (hne (h0.symm)).elim
    · have : (0:Real) < x := by
        have := (isPos_iff x).mp hp
        simpa [gt_iff_lt] using this
      exact (hnlt this).elim
    · exact hn
  rw [isNeg_def] at hxneg
  obtain ⟨b, hb, hb_cauchy, hxb⟩ := hxneg
  rw [boundedAwayNeg_def] at hb
  obtain ⟨c, cpos, hb⟩ := hb
  have claim1 : ∀ n, ¬ (c/2).Close (a n) (b n) := by
    intro n; specialize ha n; specialize hb n
    simp [Section_4_3.close_iff]
    calc
      _ < c := by linarith
      _ ≤ a n - b n := by linarith
      _ ≤ _ := le_abs_self _
  have claim2 : ¬(c/2).EventuallyClose (Sequence.ofNatFun a) (Sequence.ofNatFun b) := by
    intro hclose
    obtain ⟨N, hN⟩ := eventually_le_of_eventuallyClose hclose
    have : (c/2).Close (a N) (b N) := by
      rw [Section_4_3.close_iff]
      exact hN N le_rfl
    exact claim1 N this
  have claim3 : ¬Sequence.Equiv a b := by
    intro heq
    exact claim2 (heq (c/2) (half_pos cpos))
  simp_rw [x, LIM_eq_LIM hcauchy hb_cauchy] at hxb
  contradiction

/-- Corollary 5.4.10 -/
theorem Real.LIM_mono {a b:ℕ → ℚ} (ha: (Sequence.ofNatFun a).IsCauchy)
    (hb: (Sequence.ofNatFun b).IsCauchy) (hmono: ∀ n, a n ≤ b n) :
    LIM a ≤ LIM b := by
  have hnonneg := LIM_of_nonneg (a := b - a) (by intro n; simp [hmono n]) (Sequence.IsCauchy.sub hb ha)
  have h : LIM b - LIM a ≥ 0 := by rwa [←Real.LIM_sub hb ha] at hnonneg
  change 0 ≤ LIM b - LIM a at h
  rw [le_iff] at h ⊢
  rcases h with hlt | heq
  · left
    have hp : (LIM b - LIM a).IsPos := by
      have : LIM b - LIM a > 0 := by simpa [gt_iff_lt] using hlt
      exact (isPos_iff _).mpr this
    rw [lt_iff, neg_iff_pos_of_neg, neg_sub]
    exact hp
  · right
    exact (sub_eq_zero.mp heq.symm).symm

/-- Proposition 5.4.12 (Bounding reals by rationals) -/
theorem Real.exists_rat_le_and_nat_gt {x:Real} (hx: x.IsPos) :
    (∃ q:ℚ, q > 0 ∧ (q:Real) ≤ x) ∧ ∃ N:ℕ, x < (N:Real) := by
  rw [isPos_def] at hx; choose a hbound hcauchy heq using hx
  rw [boundedAwayPos_def] at hbound; choose q hq hbound using hbound
  have := Sequence.isBounded_of_isCauchy hcauchy
  rw [Sequence.isBounded_def] at this; choose r hr this using this
  simp [Sequence.boundedBy_def] at this
  refine ⟨ ⟨ q, hq, ?_ ⟩, ?_ ⟩
  . convert LIM_mono (Sequence.IsCauchy.const _) hcauchy hbound
    exact Real.ratCast_def q
  choose N hN using exists_nat_gt r; use N
  have hxle : x ≤ (r:Real) := by
    rw [Real.ratCast_def r]
    convert LIM_mono hcauchy (Sequence.IsCauchy.const r) _
    intro n
    have hn0 : 0 ≤ (n : ℤ) := Int.natCast_nonneg n
    have habs : |a n| ≤ r := by
      have := this n
      rw [ofNatFun_seq_of_nonneg a hn0, Int.toNat_natCast] at this
      exact this
    exact (le_abs_self _).trans habs
  have hrlt : (r:Real) < ((N:ℚ):Real) :=
    (lt_of_coe r (N:ℚ)).mp (by exact_mod_cast hN)
  have hNreal : ((N:ℚ):Real) = (N:Real) := rfl
  rw [← hNreal]
  -- x ≤ r and r < N
  rw [le_iff] at hxle
  rcases hxle with hlt | rfl
  · exact real_lt_trans hlt hrlt
  · exact hrlt

/-- Corollary 5.4.13 (Archimedean property ) -/
theorem Real.le_mul {ε:Real} (hε: ε.IsPos) (x:Real) : ∃ M:ℕ, M > 0 ∧ M * ε > x := by
  obtain rfl | hx | hx := trichotomous x
  · refine ⟨1, Nat.succ_pos 0, ?_⟩
    rw [nat_one_mul]
    simpa [gt_iff_lt] using (isPos_iff ε).mp hε
  · choose N hN using (exists_rat_le_and_nat_gt (div_of_pos hx hε)).2
    set M := N+1
    refine ⟨M, Nat.succ_pos N, ?_⟩
    have hNM : (N:Real) < (M:Real) := by
      have : (N:ℚ) < (M:ℚ) := by exact_mod_cast Nat.lt_succ_self N
      exact (lt_of_coe _ _).mp this
    have hN' : x/ε < (M:Real) := real_lt_trans hN hNM
    have hmul := mul_lt_mul_right hN' hε
    have hcancel : (x/ε) * ε = x := by
      rw [div_eq, mul_assoc, inv_mul_self (nonzero_of_pos hε)]
      change x * ((1:ℚ):Real) = x
      exact Real.mul_one x
    rwa [hcancel] at hmul
  · refine ⟨1, Nat.succ_pos 0, ?_⟩
    rw [nat_one_mul]
    have : (x - ε).IsNeg := by
      rw [neg_iff_pos_of_neg, neg_sub]
      exact pos_add hε ((neg_iff_pos_of_neg x).mp hx)
    exact (lt_iff x ε).mpr this

theorem Real.max_eq (x y:Real) : max x y = if x ≥ y then x else y := max_def' x y

theorem Real.min_eq (x y:Real) : min x y = if x ≤ y then x else y := rfl

end Chapter5
