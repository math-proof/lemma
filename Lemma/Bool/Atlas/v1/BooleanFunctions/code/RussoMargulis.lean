import Mathlib
import sympy.Basic
import Def.v1.Atlas.BooleanFunctions.code.RussoMargulis
open BooleanFourier
open Finset BigOperators


namespace BooleanFourier

/--
[flipBit_apply_same](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/RussoMargulis.lean)
-/
@[path]
lemma flipBit_apply_same
  {n : ℕ}
  {x : Fin n → Bool}
  {i : Fin n} :
-- imply
  flipBit x i i = !x i := by
-- proof
  simp [flipBit]

end BooleanFourier

namespace BooleanFourier

/--
[flipBit_apply_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/RussoMargulis.lean)
-/
@[path]
lemma flipBit_apply_ne
  {n : ℕ}
  {x : Fin n → Bool}
  {i k : Fin n}
-- given
  (h : k ≠ i) :
-- imply
  flipBit x i k = x k := by
-- proof
  simp [flipBit, h]

end BooleanFourier

namespace BooleanFourier

/--
[flipBit_flipBit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/RussoMargulis.lean)
-/
@[path]
lemma flipBit_flipBit
  {n : ℕ}
  {x : Fin n → Bool}
  {i : Fin n} :
-- imply
  flipBit (flipBit x i) i = x := by
-- proof
  ext k
  by_cases hk : k = i
  · subst hk; simp [Bool.not_not]
  · simp [hk]

end BooleanFourier

namespace BooleanFourier

/--
[hasDerivAt_factor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/RussoMargulis.lean)
-/
@[path]
lemma hasDerivAt_factor
  {b : Bool}
  {p : ℝ} :
-- imply
  HasDerivAt (fun q => if b then q else (1 : ℝ) - q) (if b then 1 else -1) p := by
-- proof
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (hasDerivAt_id p).const_sub 1
  · simp only [↓reduceIte]
    exact hasDerivAt_id p

end BooleanFourier

namespace BooleanFourier

/--
[hasDerivAt_pBiasedWeight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/RussoMargulis.lean)
-/
@[path]
lemma hasDerivAt_pBiasedWeight
  {n : ℕ}
  {x : Fin n → Bool}
  {p : ℝ} :
-- imply
  HasDerivAt (fun q => pBiasedWeight n q x) (∑ j : Fin n, (∏ i ∈ (univ : Finset (Fin n)).erase j, if x i then p else (1 - p)) * (if x j then 1 else -1)) p := by
-- proof
  unfold pBiasedWeight
  have h := HasDerivAt.fun_finset_prod (u := Finset.univ)
    (f := fun i q => if x i then q else (1 : ℝ) - q)
    (f' := fun i => if x i then 1 else -1)
    (fun i _ => hasDerivAt_factor (x i) p)
  simp only [smul_eq_mul] at h
  exact h

end BooleanFourier

namespace BooleanFourier

/--
[deriv_term_eq_influence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/RussoMargulis.lean)
-/
@[path]
lemma deriv_term_eq_influence
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {j : Fin n}
  {p : ℝ}
-- given
  (hf : IsMonotone f)
  (_hp0 : 0 < p)
  (_hp1 : p < 1) :
-- imply
  (∑ x : Fin n → Bool, ((∏ i ∈ (univ : Finset (Fin n)).erase j, if x i = true then p else 1 - p) * (if x j = true then (1 : ℝ) else -1)) * (if f x = true then (1 : ℝ) else 0)) = (∑ x : Fin n → Bool, (∏ i : Fin n, if x i = true then p else 1 - p) * (if f x ≠ f (flipBit x j) then (1 : ℝ) else 0)) := by
-- proof
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  apply Finset.sum_involution (fun x _ => flipBit x j)
  ·
    intro x _
    simp only [flipBit_flipBit, ne_eq]
    have hprod_eq : (∏ i ∈ (univ : Finset (Fin n)).erase j,
      if (flipBit x j) i = true then p else 1 - p) =
      ∏ i ∈ (univ : Finset (Fin n)).erase j, if x i = true then p else 1 - p := by
      apply Finset.prod_congr rfl
      intro i hi; simp [(Finset.mem_erase.mp hi).1]
    have hprod_x : (∏ i : Fin n, if x i = true then p else 1 - p) =
      (∏ i ∈ (univ : Finset (Fin n)).erase j, if x i = true then p else 1 - p) *
      (if x j = true then p else 1 - p) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    have hprod_flip : (∏ i : Fin n, if (flipBit x j) i = true then p else 1 - p) =
      (∏ i ∈ (univ : Finset (Fin n)).erase j, if x i = true then p else 1 - p) *
      (if !(x j) = true then p else 1 - p) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
      rw [hprod_eq]
      simp
    rw [hprod_eq, hprod_x, hprod_flip]
    simp only [flipBit_apply_same]
    set W := ∏ i ∈ (univ : Finset (Fin n)).erase j, if x i = true then p else 1 - p
    cases hxj : x j <;> cases hfx : f x <;> cases hff : f (flipBit x j) <;>
      simp_all <;> ring_nf <;> try ring
    ·
      exfalso
      have hle : x ≤ flipBit x j := Pi.le_def.mpr (fun i => by
        by_cases hi : i = j
        · subst hi; simp [hxj]
        · simp [hi])
      have := hf hle
      rw [hfx, hff] at this; exact absurd this (by decide)
    ·
      exfalso
      have hle : flipBit x j ≤ x := Pi.le_def.mpr (fun i => by
        by_cases hi : i = j
        · subst hi; simp [hxj]
        · simp [hi])
      have := hf hle
      rw [hff, hfx] at this; exact absurd this (by decide)
  ·
    intro x _ _ h
    have : (flipBit x j) j = x j := congr_fun h j
    simp at this
  ·
    intro x _; exact Finset.mem_univ _
  ·
    intro x _; exact flipBit_flipBit x j

end BooleanFourier

namespace BooleanFourier

/--
[russo_margulis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/RussoMargulis.lean)
-/
@[path]
lemma russo_margulis
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {p : ℝ}
-- given
  (hf : IsMonotone f)
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  HasDerivAt (pBiasedExpectation f) (∑ i : Fin n, pBiasedInfluence f i p) p := by
-- proof
  classical
  unfold pBiasedExpectation
  have hderiv : HasDerivAt (fun q => ∑ x : Fin n → Bool,
    pBiasedWeight n q x * if f x then 1 else 0)
    (∑ x : Fin n → Bool, (∑ j : Fin n, (∏ i ∈ (univ : Finset (Fin n)).erase j,
      if x i then p else (1 - p)) * (if x j then 1 else -1)) *
      if f x then 1 else 0) p := by
    apply HasDerivAt.fun_sum
    intro x _
    exact (hasDerivAt_pBiasedWeight n x p).mul_const _
  suffices h : (∑ x : Fin n → Bool, (∑ j : Fin n, (∏ i ∈ (univ : Finset (Fin n)).erase j,
    if x i then p else (1 - p)) * (if x j then 1 else -1)) *
    if f x then 1 else 0) = ∑ i : Fin n, pBiasedInfluence f i p by
    rw [← h]; exact hderiv
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext j
  unfold pBiasedInfluence pBiasedWeight
  exact deriv_term_eq_influence f hf j p hp0 hp1

end BooleanFourier


-- created on 2026-10-23
