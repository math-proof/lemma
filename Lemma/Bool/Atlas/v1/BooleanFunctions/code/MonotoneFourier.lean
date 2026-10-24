import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.BooleanFunctions.code.MonotoneFourier
open Finset BigOperators BooleanFourier


namespace BooleanFourier

/--
[monotone_update_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/MonotoneFourier.lean)
-/
@[path]
lemma monotone_update_le
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {i : Fin n}
  {x : Fin n → Bool}
-- given
  (hf : IsMonotone f) :
-- imply
  f (Function.update x i false) ≤ f (Function.update x i true) := by
-- proof
  apply hf
  intro j
  by_cases hij : j = i
  · subst hij; simp
  · simp [Function.update_of_ne hij]

end BooleanFourier

namespace BooleanFourier

/--
[flipCoord_flipCoord'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/MonotoneFourier.lean)
-/
@[path]
lemma flipCoord_flipCoord'
  {n : ℕ}
  {x : Fin n → Bool}
  {i : Fin n} :
-- imply
  flipCoord (flipCoord x i) i = x := by
-- proof
  ext j
  simp only [flipCoord]
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

end BooleanFourier

namespace BooleanFourier

/--
[monotone_pair_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/MonotoneFourier.lean)
-/
@[path]
lemma monotone_pair_sum
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {i : Fin n}
  {x : Fin n → Bool}
-- given
  (hf : IsMonotone f) :
-- imply
  boolToReal (f x) * boolToReal (x i) + boolToReal (f (flipCoord x i)) * boolToReal ((flipCoord x i) i) = if f x ≠ f (flipCoord x i) then 2 else 0 := by
-- proof
  have hflip_i : (flipCoord x i) i = !x i := by simp [flipCoord]
  rw [hflip_i]
  cases hxi : x i
  ·
    simp only [Bool.not_false, boolToReal_true, boolToReal_false]
    have hflip_eq : flipCoord x i = Function.update x i true := by
      ext j; simp only [flipCoord, Function.update]; split_ifs with h
      · subst h; simp [hxi]
      · rfl
    rw [hflip_eq]
    have hupd_false : Function.update x i false = x := by
      ext j; by_cases hj : j = i
      · subst hj; simp [hxi]
      · simp [Function.update_of_ne hj]
    have hmono : f x ≤ f (Function.update x i true) := by
      conv_lhs => rw [← hupd_false]
      exact monotone_update_le f hf i x
    cases hfx : f x <;> cases hfflip : f (Function.update x i true)
    · simp [boolToReal]
    · simp [boolToReal]; norm_num
    ·
      rw [hfx, hfflip] at hmono; exact absurd hmono (by decide)
    · simp [boolToReal]
  ·
    simp only [Bool.not_true, boolToReal_true, boolToReal_false]
    have hflip_eq : flipCoord x i = Function.update x i false := by
      ext j; simp only [flipCoord, Function.update]; split_ifs with h
      · subst h; simp [hxi]
      · rfl
    rw [hflip_eq]
    have hupd_true : Function.update x i true = x := by
      ext j; by_cases hj : j = i
      · subst hj; simp [hxi]
      · simp [Function.update_of_ne hj]
    have hmono : f (Function.update x i false) ≤ f x := by
      conv_rhs => rw [← hupd_true]
      exact monotone_update_le f hf i x
    cases hfx : f x <;> cases hfflip : f (Function.update x i false)
    · simp [boolToReal]
    ·
      rw [hfx, hfflip] at hmono; exact absurd hmono (by decide)
    · simp [boolToReal]; norm_num
    · simp [boolToReal]

end BooleanFourier

namespace BooleanFourier

/--
[sum_boolToReal_eq_card_of_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/MonotoneFourier.lean)
-/
@[path]
lemma sum_boolToReal_eq_card_of_monotone
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {i : Fin n}
-- given
  (hf : IsMonotone f) :
-- imply
  ∑ x : Fin n → Bool, boolToReal (f x) * boolToReal (x i) = ↑(Finset.univ.filter (fun x : Fin n → Bool => f x ≠ f (flipCoord x i))).card := by
-- proof
  classical
  have hflip_bij : Function.Bijective (fun x : Fin n → Bool => flipCoord x i) := by
    constructor
    · intro a b hab
      have := congr_arg (fun x => flipCoord x i) hab
      simp only [flipCoord_flipCoord'] at this
      exact this
    · intro y
      exact ⟨flipCoord y i, flipCoord_flipCoord' y i⟩
  have sum_flip : ∀ g : (Fin n → Bool) → ℝ,
    ∑ x : Fin n → Bool, g (flipCoord x i) = ∑ x : Fin n → Bool, g x :=
    fun g => Fintype.sum_bijective _ hflip_bij _ _ (fun _ => rfl)
  have double : (2 : ℝ) * ∑ x : Fin n → Bool, boolToReal (f x) * boolToReal (x i) =
    ∑ x : Fin n → Bool,
      (boolToReal (f x) * boolToReal (x i) +
        boolToReal (f (flipCoord x i)) * boolToReal ((flipCoord x i) i)) := by
    have heq := sum_flip (fun x => boolToReal (f x) * boolToReal (x i))
    have hdecomp : ∑ x : Fin n → Bool,
      (boolToReal (f x) * boolToReal (x i) +
        boolToReal (f (flipCoord x i)) * boolToReal ((flipCoord x i) i)) =
      ∑ x : Fin n → Bool, boolToReal (f x) * boolToReal (x i) +
      ∑ x : Fin n → Bool, boolToReal (f (flipCoord x i)) * boolToReal ((flipCoord x i) i) :=
      Finset.sum_add_distrib
    linarith
  simp_rw [monotone_pair_sum f hf i] at double
  have boole_eq : ∑ x : Fin n → Bool,
    (if f x ≠ f (flipCoord x i) then (2 : ℝ) else 0) =
    2 * ↑(Finset.univ.filter (fun x : Fin n → Bool => f x ≠ f (flipCoord x i))).card := by
    have h1 : ∑ x : Fin n → Bool,
      (if f x ≠ f (flipCoord x i) then (2 : ℝ) else 0) =
      2 * ∑ x : Fin n → Bool, (if f x ≠ f (flipCoord x i) then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]; congr 1; ext x; split_ifs <;> ring
    rw [h1, ← Finset.sum_boole]
  linarith [double, boole_eq]

end BooleanFourier

namespace BooleanFourier

/--
[fourierCoeff_singleton_eq_influence_of_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/MonotoneFourier.lean)
-/
@[path]
lemma fourierCoeff_singleton_eq_influence_of_monotone
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {i : Fin n}
-- given
  (hf : IsMonotone f) :
-- imply
  fourierCoeff (liftPM f) {i} = influence f i := by
-- proof
  classical
  simp only [fourierCoeff, liftPM, chi, influence]
  have hchi : ∀ x : Fin n → Bool, ∏ j ∈ ({i} : Finset (Fin n)), boolToReal (x j) =
    boolToReal (x i) := by
    intro x; simp
  simp_rw [hchi]
  rw [one_div, sum_boolToReal_eq_card_of_monotone f hf i]
  ring

end BooleanFourier


-- created on 2026-10-23
