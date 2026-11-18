module

public import Mathlib
public import Theorem.Analysis.Section_5_2.Part2
public import Mathlib.Algebra.Group.MinimalAxioms
public import Instance.Analysis.Section_5_3.Part8
public import Theorem.Analysis.Section_5_3.Part4
public import Theorem.Analysis.Section_5_3.Part10
public import Theorem.Analysis.Section_5_3.Part7

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

public theorem Real.inv_def {a:ℕ → ℚ} (h: BoundedAwayZero a)
    (hc: (Sequence.ofNatFun a).IsCauchy) :
    (LIM a)⁻¹ = LIM a⁻¹ := by
  have hx : LIM a ≠ 0 := lim_ne_zero_of_boundedAwayZero h hc
  set x := LIM a
  have ⟨ h1, h2, h3 ⟩ := (boundedAwayZero_of_nonzero hx).choose_spec
  simp [Inv.inv, hx]
  exact inv_of_equiv h2 h1 h hc h3.symm

@[simp]
public theorem Real.inv_zero : (0:Real)⁻¹ = 0 := by simp [Inv.inv]

public theorem BoundedAwayZero.const {q : ℚ} (hq : q ≠ 0) : BoundedAwayZero fun _ ↦ q := by
  use |q|; simp [hq]

public theorem Real.inv_ratCast (q:ℚ) : (q:Real)⁻¹ = (q⁻¹:ℚ) := by
  by_cases h : q = 0
  . rw [h, ← show (0:Real) = (0:ℚ) by norm_cast]; norm_num; norm_cast
  simp_rw [ratCast_def, inv_def (BoundedAwayZero.const h) (isCauchy_ofNatFun_const q)]; congr


public theorem Real.self_mul_inv {x:Real} (hx: x ≠ 0) : x * x⁻¹ = 1 := by
  obtain ⟨a, ha, hbaz, rfl⟩ := boundedAwayZero_of_nonzero hx
  have hinv := inv_isCauchy_of_boundedAwayZero hbaz ha
  rw [inv_def hbaz ha, LIM_mul ha hinv]
  have hfun : a * a⁻¹ = fun _ ↦ (1:ℚ) := by
    ext n
    have hn0 : a n ≠ 0 := nonzero_of_boundedAwayZero hbaz n
    simp [Pi.mul_apply, Pi.inv_apply, mul_inv_cancel₀ hn0]
  rw [hfun, ← ratCast_def 1]
  norm_cast

public theorem Real.inv_mul_self {x:Real} (hx: x ≠ 0) : x⁻¹ * x = 1 := by
  rw [mul_comm, self_mul_inv hx]

end Chapter5
