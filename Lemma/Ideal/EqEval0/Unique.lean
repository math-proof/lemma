import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


section

variable {W : Type} [CommRing W]
variable (G : Polynomial W) (u : W)

private noncomputable def step (y : W) : W := y - u * G.eval y

variable (y₀ : W)

private noncomputable def seq : ℕ → W :=
  Nat.rec (motive := fun _ => W) y₀ (fun (_ : ℕ) (ih : W) => step ih)

variable {I : Ideal W}

private lemma seq_succ
  {k : ℕ} :
  -- imply
  seq (k + 1) = seq k - u * G.eval (seq k) := by
  -- proof
  rfl

private lemma seq_spec
  -- given
  (hu : (Polynomial.derivative G).eval y₀ * u = 1)
  (hG : G.eval y₀ ∈ I) :
  -- imply
  ∀ k, seq k - y₀ ∈ I ∧ G.eval (seq k) ∈ I ^ (k + 1) := by
  -- proof
  intro k
  induction k
  · exact ⟨by simp [seq], by simpa [seq] using hG⟩
  ·
    rename_i k ih
    obtain ⟨h1, h2⟩ := ih
    set y := seq k
    have hstep : seq (k + 1) = y + (-(u * G.eval y)) := by
      rw [seq_succ, sub_eq_add_neg]
    constructor
    ·
      rw [hstep, add_sub_right_comm]
      apply I.add_mem h1 (I.neg_mem (I.mul_mem_left _ (Ideal.pow_le_self (Nat.succ_ne_zero k) h2)))
    ·
      rw [hstep]
      obtain ⟨c, hc⟩ := Polynomial.binomExpansion G y (-(u * G.eval y))
      rw [hc]
      obtain ⟨z, hz⟩ := Polynomial.evalSubFactor (Polynomial.derivative G) y₀ y
      have hdiff : (Polynomial.derivative G).eval y₀ - (Polynomial.derivative G).eval y ∈ I := by
        rw [hz]
        apply I.mul_mem_left _
        ·
          rw [← neg_sub]
          apply I.neg_mem h1
      have hkey : G.eval y + (Polynomial.derivative G).eval y * -(u * G.eval y) =
        G.eval y * (((Polynomial.derivative G).eval y₀ - (Polynomial.derivative G).eval y) * u) := by
        linear_combination (-(G.eval y)) * hu
      rw [hkey]
      refine (I ^ (k + 1 + 1)).add_mem ?_ ?_
      ·
        rw [pow_succ]
        apply Ideal.mul_mem_mul h2 (I.mul_mem_right _ hdiff)
      ·
        have : c * (-(u * G.eval y)) ^ 2 = (c * u ^ 2) * (G.eval y * G.eval y) := by ring
        rw [this, pow_succ]
        apply Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul h2 (Ideal.pow_le_self (Nat.succ_ne_zero k) h2))

private lemma seq_succ_sub_mem
  {k : ℕ}
  -- given
  (hu : (Polynomial.derivative G).eval y₀ * u = 1)
  (hG : G.eval y₀ ∈ I) :
  -- imply
  seq (k + 1) - seq k ∈ I ^ (k + 1) := by
  -- proof
  rw [seq_succ, sub_sub_cancel_left]
  apply (I ^ (k + 1)).neg_mem (Ideal.mul_mem_left _ _ ((seq_spec hu hG k).2))

private lemma seq_cauchy
  {m n : ℕ}
  -- given
  (hu : (Polynomial.derivative G).eval y₀ * u = 1)
  (hG : G.eval y₀ ∈ I)
  (hmn : m ≤ n) :
  -- imply
  seq n - seq m ∈ I ^ m := by
  -- proof
  induction n, hmn using Nat.le_induction
  · simp
  ·
    rename_i n hmn ih
    have : seq (n + 1) - seq m = (seq (n + 1) - seq n) + (seq n - seq m) := by ring
    rw [this]
    apply (I ^ m).add_mem (Ideal.pow_le_pow_right (by omega) (seq_succ_sub_mem hu hG (k := n))) ih

end

private lemma smod_iff
  {W : Type} [CommRing W]
  {I : Ideal W}
  {n : ℕ}
  {x y : W} :
  -- imply
  x ≡ y [SMOD (I ^ n • ⊤ : Submodule W W)] ↔ x - y ∈ I ^ n := by
  -- proof
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

private lemma isUnit_add_of_mem
  {W : Type} [CommRing W]
  {I : Ideal W} [IsAdicComplete I W]
  {v a : W}
  -- given
  (hv : IsUnit v)
  (ha : a ∈ I) :
  -- imply
  IsUnit (v + a) := by
  -- proof
  have hj := IsAdicComplete.le_jacobson_bot I ha
  rw [Ideal.mem_jacobson_bot] at hj
  obtain ⟨w, rfl⟩ := hv
  have h1 : IsUnit (a * (↑w⁻¹ : W) + 1) := hj _
  have : (↑w : W) + a = ↑w * (a * ↑w⁻¹ + 1) := by
    rw [mul_add, mul_one, ← mul_assoc, mul_comm (↑w : W) a, mul_assoc, Units.mul_inv, mul_one, add_comm]
  rw [this]
  apply (Units.isUnit w).mul h1

private lemma helper_main
  {W : Type} [CommRing W]
  {I : Ideal W} [IsAdicComplete I W]
  (G : Polynomial W)
  (y₀ : W)
  -- given
  (hG : G.eval y₀ ∈ I)
  (hG' : IsUnit ((Polynomial.derivative G).eval y₀)) :
  -- imply
  ∃! y : W, y - y₀ ∈ I ∧ G.eval y = 0 := by
  -- proof
  obtain ⟨uu, huu⟩ := hG'
  set u : W := ↑uu⁻¹ with hu
  have hu1 : (Polynomial.derivative G).eval y₀ * u = 1 := by
    rw [← huu, hu, Units.mul_inv]
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → seq G u y₀ m ≡ seq G u y₀ n [SMOD (I ^ m • ⊤ : Submodule W W)] := by
    intro m n hmn
    rw [smod_iff, ← neg_sub]
    apply (I ^ m).neg_mem (seq_cauchy G u y₀ hu1 hG hmn)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (seq G u y₀) hcauchy
  have hL' : ∀ n, seq G u y₀ n - L ∈ I ^ n := fun n => (smod_iff).mp (hL n)
  have hroot : G.eval L = 0 := by
    refine IsHausdorff.haus' (I := I) (G.eval L) fun n => ?_
    rw [smod_iff, sub_zero]
    obtain ⟨z, hz⟩ := Polynomial.evalSubFactor G L (seq G u y₀ n)
    have : G.eval L = (G.eval L - G.eval (seq G u y₀ n)) + G.eval (seq G u y₀ n) := by ring
    rw [this, hz]
    refine (I ^ n).add_mem ?_ ?_
    ·
      apply Ideal.mul_mem_left _ _
      ·
        rw [← neg_sub]
        apply (I ^ n).neg_mem (hL' n)
    · apply Ideal.pow_le_pow_right (Nat.le_succ n) ((seq_spec G u y₀ hu1 hG n).2)
  have hcong : L - y₀ ∈ I := by
    have h1 : seq G u y₀ 1 - L ∈ I ^ 1 := hL' 1
    rw [pow_one] at h1
    have h2 := (seq_spec G u y₀ hu1 hG 1).1
    have : L - y₀ = (seq G u y₀ 1 - y₀) - (seq G u y₀ 1 - L) := by ring
    rw [this]
    apply I.sub_mem h2 h1
  refine ⟨L, ⟨hcong, hroot⟩, ?_⟩
  intro y hy
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨c, hc⟩ := Polynomial.binomExpansion G L (y - L)
  rw [add_sub_cancel, hy2, hroot, zero_add] at hc
  have hfac : (y - L) * ((Polynomial.derivative G).eval L + c * (y - L)) = 0 := by
    linear_combination -hc
  have hyL : y - L ∈ I := by
    have : y - L = (y - y₀) - (L - y₀) := by ring
    rw [this]
    apply I.sub_mem hy1 hcong
  have hunit : IsUnit ((Polynomial.derivative G).eval L + c * (y - L)) := by
    obtain ⟨z, hz⟩ := Polynomial.evalSubFactor (Polynomial.derivative G) L y₀
    have : (Polynomial.derivative G).eval L + c * (y - L) =
        (Polynomial.derivative G).eval y₀ + (z * (L - y₀) + c * (y - L)) := by
      linear_combination hz
    rw [this]
    apply isUnit_add_of_mem ⟨uu, huu⟩ (I.add_mem (I.mul_mem_left _ hcong) (I.mul_mem_left _ hyL))
  rw [mul_comm] at hfac
  apply sub_eq_zero.mp ((hunit.mul_right_eq_zero).mp hfac)

/--
[Ideal_existsUnique_sub_mem_and_eval_eq_zero_of_isUnit_derivative](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_existsUnique_sub_mem_and_eval_eq_zero_of_isUnit_derivative.lean)
-/
@[path]
private lemma main
  {W : Type} [CommRing W]
  {I : Ideal W} [IsAdicComplete I W]
  {G : Polynomial W}
  {y₀ : W}
  -- given
  (hG : G.eval y₀ ∈ I)
  (hG' : IsUnit ((Polynomial.derivative G).eval y₀)) :
  -- imply
  ∃! y : W, y - y₀ ∈ I ∧ G.eval y = 0 := by
  -- proof
  apply helper_main G y₀ hG hG'


-- created on 2026-10-20
