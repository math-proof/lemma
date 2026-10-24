import Mathlib
import sympy.Basic
open scoped BigOperators
open Finset Nat


namespace Nat.SylvesterSchur

/--
[cube_le_two_pow_of_ten_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma cube_le_two_pow_of_ten_le {m : ℕ} (hm : 10 ≤ m) : m ^ 3 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    calc
      (m + 1) ^ 3 ≤ 2 * m ^ 3 := by
        nlinarith [hm, sq_nonneg (m : ℤ), sq_nonneg ((m : ℤ) - 3)]
      _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (m + 1) := by ring

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[sqrt_two_mul_add_two_le_div_fifteen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma sqrt_two_mul_add_two_le_div_fifteen {n : ℕ} (hn : 512 ≤ n) :
  Nat.sqrt (2 * n + 2) ≤ n / 15 := by
  let s := Nat.sqrt (2 * n + 2)
  have hs2 : s ^ 2 ≤ 2 * n + 2 := by
    dsimp [s]
    exact Nat.sqrt_le' (2 * n + 2)
  have hpoly : 225 * (2 * n + 2) ≤ n ^ 2 := by nlinarith [hn]
  have hsq : (15 * s) ^ 2 ≤ n ^ 2 := by
    calc
      (15 * s) ^ 2 = 225 * s ^ 2 := by ring
      _ ≤ 225 * (2 * n + 2) := Nat.mul_le_mul_left 225 hs2
      _ ≤ n ^ 2 := hpoly
  have h15 : 15 * s ≤ n := by
    exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hsq
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 15)]
  omega

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[nthRoot_three_two_mul_add_two_sq_le_div_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma nthRoot_three_two_mul_add_two_sq_le_div_four {n : ℕ} (hn : 512 ≤ n) :
  (Nat.nthRoot 3 (2 * n + 2)) ^ 2 ≤ n / 4 := by
  let c := Nat.nthRoot 3 (2 * n + 2)
  have hc3 : c ^ 3 ≤ 2 * n + 2 := by
    dsimp [c]
    exact Nat.pow_nthRoot_le (Or.inl (by norm_num : 3 ≠ 0))
  have hpoly : 64 * (2 * n + 2) ^ 2 ≤ n ^ 3 := by nlinarith [hn]
  have hcube : (4 * c ^ 2) ^ 3 ≤ n ^ 3 := by
    calc
      (4 * c ^ 2) ^ 3 = 64 * (c ^ 3) ^ 2 := by ring
      _ ≤ 64 * (2 * n + 2) ^ 2 :=
        Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left hc3 2)
      _ ≤ n ^ 3 := hpoly
  have h4 : 4 * c ^ 2 ≤ n := by
    exact (Nat.pow_le_pow_iff_left (by norm_num : 3 ≠ 0)).mp hcube
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr
    (by simpa [c, two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h4)

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[log_two_two_mul_add_two_le_nthRoot_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma log_two_two_mul_add_two_le_nthRoot_three {n : ℕ} (hn : 512 ≤ n) :
  Nat.log 2 (2 * n + 2) ≤ Nat.nthRoot 3 (2 * n + 2) := by
  let N := 2 * n + 2
  let c := Nat.nthRoot 3 N
  have hc10 : 10 ≤ c := by
    dsimp [c, N]
    rw [Nat.le_nthRoot_iff (by norm_num : 3 ≠ 0)]
    norm_num
    omega
  have hNlt : N < (c + 1) ^ 3 := by
    exact (Nat.nthRoot_lt_iff (by norm_num : 3 ≠ 0)).mp (Nat.lt_succ_self c)
  have hcube : (c + 1) ^ 3 ≤ 2 ^ (c + 1) :=
    cube_le_two_pow_of_ten_le (by omega : 10 ≤ c + 1)
  have hNpow : N < 2 ^ (c + 1) := hNlt.trans_le hcube
  have hlog : Nat.log 2 N < c + 1 :=
    Nat.log_lt_of_lt_pow (by dsimp [N]; omega) hNpow
  dsimp [c, N] at hlog ⊢
  omega

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[self_le_four_pow_div_one_twenty_eight_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma self_le_four_pow_div_one_twenty_eight_add_one {n : ℕ} (hn : 512 ≤ n) :
  n ≤ 4 ^ (n / 128 + 1) := by
  let m := n / 128
  have hm4 : 4 ≤ m := by
    dsimp [m]
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 128)]
    omega
  have hnlt : n < 128 * (m + 1) := by
    dsimp [m]
    exact Nat.lt_mul_div_succ n (by norm_num : 0 < 128)
  have hmul_general : ∀ m : ℕ, 4 ≤ m → 128 * (m + 1) ≤ 4 ^ (m + 1) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      calc
        128 * (m + 1 + 1) ≤ 4 * (128 * (m + 1)) := by nlinarith
      _ ≤ 4 * 4 ^ (m + 1) := Nat.mul_le_mul_left 4 ih
      _ = 4 ^ (m + 1 + 1) := by ring
  exact hnlt.le.trans (hmul_general m hm4)

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[nthRoot_two_le_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma nthRoot_two_le_sqrt (N : ℕ) : Nat.nthRoot 2 N ≤ Nat.sqrt N := by
  rw [Nat.le_sqrt']
  exact Nat.pow_nthRoot_le (Or.inl (by norm_num : 2 ≠ 0))

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[nthRoot_le_sqrt_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma nthRoot_le_sqrt_of_two_le {N m : ℕ} (hm : 2 ≤ m) :
  Nat.nthRoot m N ≤ Nat.sqrt N := by
  let s := Nat.sqrt N
  have hNlt : N < (s + 1) ^ 2 := by
    exact Nat.sqrt_lt'.mp (Nat.lt_succ_self s)
  have hpow : (s + 1) ^ 2 ≤ (s + 1) ^ m := by
    apply Nat.pow_le_pow_right
    · omega
    · exact hm
  have hlt : Nat.nthRoot m N < s + 1 := by
    rw [Nat.nthRoot_lt_iff (by omega : m ≠ 0)]
    exact hNlt.trans_le hpow
  dsimp [s] at hlt ⊢
  omega

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[nthRoot_le_nthRoot_three_of_three_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma nthRoot_le_nthRoot_three_of_three_le {N m : ℕ} (hm : 3 ≤ m) :
  Nat.nthRoot m N ≤ Nat.nthRoot 3 N := by
  let c := Nat.nthRoot 3 N
  have hNlt : N < (c + 1) ^ 3 := by
    exact (Nat.nthRoot_lt_iff (by norm_num : 3 ≠ 0)).mp (Nat.lt_succ_self c)
  have hpow : (c + 1) ^ 3 ≤ (c + 1) ^ m := by
    apply Nat.pow_le_pow_right
    · omega
    · exact hm
  have hlt : Nat.nthRoot m N < c + 1 := by
    rw [Nat.nthRoot_lt_iff (by omega : m ≠ 0)]
    exact hNlt.trans_le hpow
  dsimp [c] at hlt ⊢
  omega

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[erdos_layers_tail_le_four_pow_of_nthRoot_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma erdos_layers_tail_le_four_pow_of_nthRoot_le {N r B : ℕ}
  {s : Finset ℕ}
  (hroot : ∀ j ∈ s, Nat.nthRoot (j + 1) N ≤ B)
  (hzero : ∀ j ∈ s, j ≠ 0) (hcard : s.card ≤ Nat.log 2 N) :
  (∏ j ∈ s, if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N)) ≤
    (4 ^ B) ^ Nat.log 2 N := by
  calc
    (∏ j ∈ s, if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N))
      ≤ ∏ _j ∈ s, 4 ^ B := by
        exact Finset.prod_le_prod' fun j hj => by
          have hj0 : j ≠ 0 := hzero j hj
          simpa [hj0] using (primorial_mono (hroot j hj)).trans (primorial_le_four_pow B)
    _ = (4 ^ B) ^ s.card := by rw [Finset.prod_const]
    _ ≤ (4 ^ B) ^ Nat.log 2 N :=
      Nat.pow_le_pow_right (pow_pos (by norm_num : 0 < 4) B) hcard

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[erdos_layers_tail_le_four_pow_cuberoot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma erdos_layers_tail_le_four_pow_cuberoot (N r : ℕ) :
  (∏ j ∈ ((Finset.range (Nat.log 2 N)).erase 0).erase 1,
    if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N)) ≤
    (4 ^ Nat.nthRoot 3 N) ^ Nat.log 2 N := by
  exact erdos_layers_tail_le_four_pow_of_nthRoot_le
    (s := ((Finset.range (Nat.log 2 N)).erase 0).erase 1)
    (B := Nat.nthRoot 3 N)
    (fun j hj => nthRoot_le_nthRoot_three_of_three_le (N := N) (m := j + 1) (by
      have hj_ne1 : j ≠ 1 := by simpa using (Finset.mem_erase.mp hj).1
      have hj_ne0 : j ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      omega))
    (fun j hj => (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1)
    (by
      have hcard :
        (((Finset.range (Nat.log 2 N)).erase 0).erase 1).card ≤
          (Finset.range (Nat.log 2 N)).card :=
        Finset.card_le_card fun j hj =>
          (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).2
      simpa using hcard)

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[erdos_layers_le_four_pow_three_layers_of_zero_one_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma erdos_layers_le_four_pow_three_layers_of_zero_one_mem
  (N r : ℕ) (h0 : 0 ∈ Finset.range (Nat.log 2 N))
  (h1 : 1 ∈ (Finset.range (Nat.log 2 N)).erase 0) :
  (∏ j ∈ Finset.range (Nat.log 2 N),
    if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N)) ≤
    4 ^ (r + Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N) := by
  let c := Nat.nthRoot 3 N
  have hf0 : primorial r ≤ 4 ^ r := primorial_le_four_pow r
  have hf1 : primorial (Nat.nthRoot 2 N) ≤ 4 ^ Nat.sqrt N :=
    (primorial_mono (nthRoot_two_le_sqrt N)).trans (primorial_le_four_pow (Nat.sqrt N))
  have hrest :
    (∏ j ∈ ((Finset.range (Nat.log 2 N)).erase 0).erase 1,
      if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N)) ≤
      (4 ^ c) ^ Nat.log 2 N := by
    simpa [c] using erdos_layers_tail_le_four_pow_cuberoot N r
  calc
    (∏ j ∈ Finset.range (Nat.log 2 N),
      if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N))
      = primorial r *
        (primorial (Nat.nthRoot 2 N) *
          ∏ j ∈ ((Finset.range (Nat.log 2 N)).erase 0).erase 1,
            if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N)) := by
        rw [← Finset.mul_prod_erase (Finset.range (Nat.log 2 N))
          (fun j => if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N)) h0,
          ← Finset.mul_prod_erase ((Finset.range (Nat.log 2 N)).erase 0)
            (fun j => if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N))
            h1]
        simp
    _ ≤ 4 ^ r * (4 ^ Nat.sqrt N * (4 ^ c) ^ Nat.log 2 N) :=
      Nat.mul_le_mul hf0 (Nat.mul_le_mul hf1 hrest)
    _ = 4 ^ (r + Nat.sqrt N + c * Nat.log 2 N) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
      ring_nf
    _ = 4 ^ (r + Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N) := by
      dsimp [c]

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[erdos_layers_le_four_pow_three_layers_of_zero_mem_not_one_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma erdos_layers_le_four_pow_three_layers_of_zero_mem_not_one_mem
  (N r : ℕ) (h0 : 0 ∈ Finset.range (Nat.log 2 N))
  (h1 : 1 ∉ (Finset.range (Nat.log 2 N)).erase 0) :
  (∏ j ∈ Finset.range (Nat.log 2 N),
    if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N)) ≤
    4 ^ (r + Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N) := by
  have hlog_pos : 0 < Nat.log 2 N := Finset.mem_range.mp h0
  have hlog_le_one : Nat.log 2 N ≤ 1 := by
    by_contra hle
    push Not at hle
    have h1mem : 1 ∈ (Finset.range (Nat.log 2 N)).erase 0 := by
      exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
    exact h1 h1mem
  have hlog : Nat.log 2 N = 1 := by omega
  calc
    (∏ j ∈ Finset.range (Nat.log 2 N),
      if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N))
      = primorial r := by simp [hlog]
    _ ≤ 4 ^ r := primorial_le_four_pow r
    _ ≤ 4 ^ (r + Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N) := by
      apply Nat.pow_le_pow_right (by norm_num : 0 < 4)
      omega

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[erdos_layers_le_four_pow_three_layers_of_zero_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma erdos_layers_le_four_pow_three_layers_of_zero_not_mem
  (N r : ℕ) (h0 : 0 ∉ Finset.range (Nat.log 2 N)) :
  (∏ j ∈ Finset.range (Nat.log 2 N),
    if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N)) ≤
    4 ^ (r + Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N) := by
  have hlog : Nat.log 2 N = 0 := by
    rw [Finset.mem_range] at h0
    omega
  simpa [hlog] using
    Nat.succ_le_of_lt (pow_pos (by norm_num : 0 < 4) (r + Nat.sqrt N))

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[erdos_layers_le_four_pow_three_layers_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma erdos_layers_le_four_pow_three_layers_aux (N r : ℕ) :
  (∏ j ∈ Finset.range (Nat.log 2 N),
    if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N)) ≤
    4 ^ (r + Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N) := by
  by_cases h0 : 0 ∈ Finset.range (Nat.log 2 N)
  · by_cases h1 : 1 ∈ (Finset.range (Nat.log 2 N)).erase 0
    · exact erdos_layers_le_four_pow_three_layers_of_zero_one_mem N r h0 h1
    · exact erdos_layers_le_four_pow_three_layers_of_zero_mem_not_one_mem N r h0 h1
  · exact erdos_layers_le_four_pow_three_layers_of_zero_not_mem N r h0

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[central_layers_two_mul_add_two_le_four_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma central_layers_two_mul_add_two_le_four_pow {n : ℕ} (hn : 512 ≤ n) :
  (∏ j ∈ Finset.range (Nat.log 2 (2 * n + 2)),
    if j = 0 then primorial ((2 * n + 2) / 3)
    else primorial (Nat.nthRoot (j + 1) (2 * n + 2))) ≤
    4 ^ ((2 * n + 2) / 3 + n / 15 + n / 4) := by
  let N := 2 * n + 2
  let L := Nat.log 2 N
  let c := Nat.nthRoot 3 N
  have hsqrt : Nat.sqrt N ≤ n / 15 := by
    dsimp [N]
    simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      sqrt_two_mul_add_two_le_div_fifteen hn
  have hlog_le_c : L ≤ c := by
    dsimp [L, c, N]
    simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      log_two_two_mul_add_two_le_nthRoot_three hn
  have hc_sq : c ^ 2 ≤ n / 4 := by
    dsimp [c, N]
    simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      nthRoot_three_two_mul_add_two_sq_le_div_four hn
  have hcL : c * L ≤ n / 4 := by
    calc
      c * L ≤ c * c := Nat.mul_le_mul_left c hlog_le_c
      _ = c ^ 2 := by ring
      _ ≤ n / 4 := hc_sq
  calc
    (∏ j ∈ Finset.range (Nat.log 2 (2 * n + 2)),
      if j = 0 then primorial ((2 * n + 2) / 3)
      else primorial (Nat.nthRoot (j + 1) (2 * n + 2)))
      ≤ 4 ^ (N / 3 + Nat.sqrt N + c * L) := by
        simpa [N, L, c] using erdos_layers_le_four_pow_three_layers_aux N (N / 3)
    _ ≤ 4 ^ ((2 * n + 2) / 3 + n / 15 + n / 4) := by
      dsimp [N] at hsqrt hcL ⊢
      apply Nat.pow_le_pow_right (by norm_num : 0 < 4)
      omega

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[central_erdos_layers_two_mul_add_two_lt_four_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
lemma central_erdos_layers_two_mul_add_two_lt_four_pow
  {n : ℕ}
-- given
  (hn : 512 ≤ n) :
-- imply
  n * (∏ j ∈ Finset.range (Nat.log 2 (2 * n + 2)),
    if j = 0 then primorial ((2 * n + 2) / 3)
    else primorial (Nat.nthRoot (j + 1) (2 * n + 2))) < 4 ^ n := by
-- proof
  have hprod := central_layers_two_mul_add_two_le_four_pow hn
  have hnfac := self_le_four_pow_div_one_twenty_eight_add_one hn
  have hexp : (2 * n + 2) / 3 + n / 15 + n / 4 + (n / 128 + 1) < n := by
    omega
  calc
    n * (∏ j ∈ Finset.range (Nat.log 2 (2 * n + 2)),
      if j = 0 then primorial ((2 * n + 2) / 3)
      else primorial (Nat.nthRoot (j + 1) (2 * n + 2)))
      ≤ 4 ^ (n / 128 + 1) * 4 ^ ((2 * n + 2) / 3 + n / 15 + n / 4) :=
        Nat.mul_le_mul hnfac hprod
    _ = 4 ^ ((n / 128 + 1) + ((2 * n + 2) / 3 + n / 15 + n / 4)) := by
      rw [← pow_add]
    _ < 4 ^ n := by
      apply Nat.pow_lt_pow_right (by norm_num : 1 < 4)
      omega

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[erdos_layers_tail_le_four_pow_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma erdos_layers_tail_le_four_pow_sqrt (N r : ℕ) :
  (∏ j ∈ (Finset.range (Nat.log 2 N)).erase 0,
    if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N)) ≤
    (4 ^ Nat.sqrt N) ^ Nat.log 2 N := by
  exact erdos_layers_tail_le_four_pow_of_nthRoot_le
    (s := (Finset.range (Nat.log 2 N)).erase 0) (B := Nat.sqrt N)
    (fun j hj => nthRoot_le_sqrt_of_two_le (N := N) (m := j + 1) (by
      have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
      omega))
    (fun j hj => (Finset.mem_erase.mp hj).1)
    (by
      have hcard :
        ((Finset.range (Nat.log 2 N)).erase 0).card ≤
          (Finset.range (Nat.log 2 N)).card :=
        Finset.card_le_card fun j hj => (Finset.mem_erase.mp hj).2
      simpa using hcard)

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[erdos_layers_le_four_pow_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma erdos_layers_le_four_pow_aux (N r : ℕ) :
  (∏ j ∈ Finset.range (Nat.log 2 N),
    if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N)) ≤
    4 ^ (r + Nat.sqrt N * Nat.log 2 N) := by
  by_cases h0 : 0 ∈ Finset.range (Nat.log 2 N)
  · have hf0 : primorial r ≤ 4 ^ r := primorial_le_four_pow r
    have hrest :
      (∏ j ∈ (Finset.range (Nat.log 2 N)).erase 0,
        if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N)) ≤
        (4 ^ Nat.sqrt N) ^ Nat.log 2 N :=
      erdos_layers_tail_le_four_pow_sqrt N r
    calc
      (∏ j ∈ Finset.range (Nat.log 2 N),
        if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N))
        = primorial r *
          ∏ j ∈ (Finset.range (Nat.log 2 N)).erase 0,
            if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N) := by
          rw [← Finset.mul_prod_erase (Finset.range (Nat.log 2 N))
            (fun j => if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N))
            h0]
          simp
      _ ≤ 4 ^ r * (4 ^ Nat.sqrt N) ^ Nat.log 2 N := Nat.mul_le_mul hf0 hrest
      _ = 4 ^ (r + Nat.sqrt N * Nat.log 2 N) := by
        rw [← pow_mul, ← pow_add]
  · have hlog : Nat.log 2 N = 0 := by
    rw [Finset.mem_range] at h0
    omega
    simpa [hlog] using Nat.succ_le_of_lt (pow_pos (by norm_num : 0 < 4) r)

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[erdos_layers_le_four_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
lemma erdos_layers_le_four_pow
  {N r : ℕ} :
-- imply
  (∏ j ∈ Finset.range (Nat.log 2 N),
    if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N)) ≤
    4 ^ (r + Nat.sqrt N * Nat.log 2 N) :=
-- proof
erdos_layers_le_four_pow_aux N r

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[erdos_layers_le_four_pow_three_layers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
lemma erdos_layers_le_four_pow_three_layers
  {N r : ℕ} :
-- imply
  (∏ j ∈ Finset.range (Nat.log 2 N),
    if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N)) ≤
    4 ^ (r + Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N) := by
-- proof
  exact erdos_layers_le_four_pow_three_layers_aux N r

end Nat.SylvesterSchur


-- created on 2026-10-20
-- updated on 2026-10-23
