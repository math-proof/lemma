module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Monotone.booleanFourier.flipCoord_le_of_true
open BooleanFourier Bool


public section

/--
[monotone_fourierCoeff_singleton_eq_influence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Monotone.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {i : Fin n}
-- given
  (hf : Monotone f) :
-- imply
  fourierCoeff (fun x => boolToReal (f x)) {i} = influence f i := by
-- proof
  simp only [BooleanFourier.fourierCoeff, chi_singleton, influence]
  have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)
  suffices h : (∑ x : Fin n → Bool, boolToReal (f x) * boolToReal (x i) : ℝ) =
    ((Finset.univ.filter fun x => f x ≠ f (flipCoord x i)).card : ℝ) by
    rw [one_div, ← h]; ring
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun x => f x ≠ f (flipCoord x i))
    (fun x => boolToReal (f x) * boolToReal (x i))
  have hfilt : ∑ x ∈ Finset.univ.filter (fun x => f x ≠ f (flipCoord x i)),
    boolToReal (f x) * boolToReal (x i) =
    ((Finset.univ.filter fun x => f x ≠ f (flipCoord x i)).card : ℝ) := by
    have hterm : ∀ x ∈ Finset.univ.filter (fun x => f x ≠ f (flipCoord x i)),
      boolToReal (f x) * boolToReal (x i) = (1 : ℝ) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, _root_.true_and] at hx
      cases hxi : x i
      case false =>
        obtain ⟨hfx, _⟩ := Bool.false_true_of_le_ne (hf (le_flipCoord_of_false hxi)) hx
        rw [hfx]; simp [boolToReal]
      case true =>
        obtain ⟨_, hfx⟩ := Bool.false_true_of_le_ne (hf (flipCoord_le_of_true hxi)) hx.symm
        rw [hfx]; simp [boolToReal]
    rw [Finset.sum_congr rfl hterm]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hcompl : ∑ x ∈ Finset.univ.filter (fun x => ¬(f x ≠ f (flipCoord x i))),
    boolToReal (f x) * boolToReal (x i) = 0 := by
    apply Finset.sum_involution (fun x _ => flipCoord x i)
    ·
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, _root_.true_and, Classical.not_not] at hx
      have h1 : f (flipCoord x i) = f x := hx.symm
      have h2 : (flipCoord x i) i = !(x i) := by simp [flipCoord]
      rw [h1, h2]
      have hzero : boolToReal (x i) + boolToReal (!(x i)) = 0 := by
        cases (x i) <;> simp [boolToReal]
      have hcancel : boolToReal (f x) * boolToReal (x i) +
        boolToReal (f x) * boolToReal (!(x i)) = 0 := calc
        _ = boolToReal (f x) * (boolToReal (x i) + boolToReal (!(x i))) := by ring
        _ = boolToReal (f x) * 0 := by rw [hzero]
        _ = 0 := by ring
      linarith [hcancel]
    ·
      intro x _ _
      exact flipCoord_ne_self'
    ·
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, _root_.true_and, Classical.not_not] at hx ⊢
      simpa only [flipCoord_flipCoord] using hx.symm
    ·
      intro x _
      exact flipCoord_flipCoord
  linarith [hsplit]


theorem BooleanFourier.monotone_fourierCoeff_singleton_eq_influence
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {i : Fin n}
-- given
  (hf : Monotone f) :
-- imply
  fourierCoeff (fun x => boolToReal (f x)) {i} = influence f i :=
-- proof
  main hf


-- created on 2026-10-23
-- updated on 2026-11-24
