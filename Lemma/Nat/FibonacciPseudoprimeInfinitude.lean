import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[wanted_fib_matrix_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma wanted_fib_matrix_pow (R : Type*) [CommRing R] (n : ℕ) :
  (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R) ^ (n+1) =
  !![(Nat.fib (n+2) : R), (Nat.fib (n+1) : R); (Nat.fib (n+1) : R), (Nat.fib n : R)] := by
  induction n with
  | zero => simp [pow_one, Nat.fib_two]
  | succ n ih =>
    rw [pow_succ, ih]
    have hS : (n + 1) + 1 = n + 2 := by omega
    ext i j
    fin_cases i
    · fin_cases j
      · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one,
        mul_one, mul_zero, add_zero, zero_add]
        rw [Nat.fib_add_two (n := n + 1), hS, Nat.cast_add]
        ring
      · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one,
        mul_one, mul_zero, add_zero, zero_add]
    · fin_cases j
      · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one,
        mul_one, mul_zero, add_zero, zero_add]
        rw [hS, Nat.fib_add_two, Nat.cast_add]
        ring
      · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one,
        mul_one, mul_zero, add_zero, zero_add]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wanted_S_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma wanted_S_sq (p : ℕ) [Fact (Nat.Prime p)] :
  (!![0, 5; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ 2 =
  (!![5, 0; 0, 5] : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one] <;>
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wanted_S_sq_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma wanted_S_sq_smul (p : ℕ) [Fact (Nat.Prime p)] :
  (!![0, 5; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ 2
    = 5 • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  rw [wanted_S_sq p, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.mk_zero, Fin.mk_one, Matrix.smul_apply, smul_eq_mul] <;>
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wanted_diag_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma wanted_diag_pow (p : ℕ) [Fact (Nat.Prime p)] (m : ℕ) :
  (!![5, 0; 0, 5] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ m =
  !![((5 : ZMod p) ^ m), 0; 0, ((5 : ZMod p) ^ m)] := by
  induction m with
  | zero =>
    simp only [pow_zero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Fin.mk_zero, Fin.mk_one, Matrix.one_apply_eq, Matrix.one_apply_ne,
        pow_zero] <;>
      rfl
  | succ m ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one,
        mul_one, mul_zero, add_zero, zero_add, pow_succ] <;>
      ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wanted_S_odd_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma wanted_S_odd_pow (p : ℕ) [Fact (Nat.Prime p)] (m : ℕ) :
  (!![0, 5; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ (2 * m + 1) =
  !![0, ((5 : ZMod p) ^ (m + 1)); ((5 : ZMod p) ^ m), 0] := by
  induction m with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, pow_one, pow_zero, pow_one]
  | succ m ih =>
    have h : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
    rw [h, pow_add, ih, wanted_S_sq p]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one,
        mul_one, mul_zero, add_zero, zero_add, pow_succ] <;>
      ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wanted_half_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma wanted_half_add (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
  ((Nat.fib n : ZMod p) + (Nat.fib (n + 2) : ZMod p)) + (Nat.fib (n + 1) : ZMod p)
    = 2 * (Nat.fib (n + 2) : ZMod p) := by
  have h := @Nat.fib_add_two n
  have c : ((Nat.fib (n + 2) : ZMod p))
    = (Nat.fib n : ZMod p) + (Nat.fib (n + 1) : ZMod p) := by
    rw [h, Nat.cast_add]
  rw [c]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wanted_half_add5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma wanted_half_add5 (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
  ((Nat.fib n : ZMod p) + (Nat.fib (n + 2) : ZMod p))
    + 5 * (Nat.fib (n + 1) : ZMod p)
    = 2 * ((Nat.fib (n + 1) : ZMod p) + (Nat.fib (n + 3) : ZMod p)) := by
  have h1 := @Nat.fib_add_two n
  have h2 := @Nat.fib_add_two (n + 1)
  have hS : (n + 1) + 1 = n + 2 := by omega
  have h3 : (n + 1) + 2 = n + 3 := by omega
  rw [h3] at h2
  rw [hS] at h2
  have c1 : ((Nat.fib (n + 2) : ZMod p))
    = (Nat.fib n : ZMod p) + (Nat.fib (n + 1) : ZMod p) := by
    rw [h1, Nat.cast_add]
  have c2 : ((Nat.fib (n + 3) : ZMod p))
    = (Nat.fib (n + 1) : ZMod p) + (Nat.fib (n + 2) : ZMod p) := by
    rw [h2, Nat.cast_add]
  rw [c2, c1]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wanted_double_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma wanted_double_mul (p : ℕ) [Fact (Nat.Prime p)] (a b : ZMod p)
  (S : Matrix (Fin 2) (Fin 2) (ZMod p))
  (hS : S ^ 2 = 5 • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))) :
  (1 + S) * (a • 1 + b • S)
    = (a + 5 * b) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) + (a + b) • S := by
  have e1 : (1 + S) * (a • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) + b • S)
    = a • 1 + b • S + (a • S + b • (S * S)) := by
    simp only [add_mul, one_mul, mul_add, mul_smul_comm, mul_one, smul_add]
    abel
  rw [e1, ← pow_two, hS]
  module

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wanted_T_double](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma wanted_T_double (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
  (2 : ZMod p) • ((((1 : Matrix (Fin 2) (Fin 2) (ZMod p))
    + !![0, 5; 1, 0]) ^ (n + 1)))
  = ((2 ^ (n + 1) * ((Nat.fib n : ZMod p) + (Nat.fib (n + 2) : ZMod p)))
    • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))
    + (2 ^ (n + 1) * (Nat.fib (n + 1) : ZMod p))
      • !![0, 5; 1, 0]) := by
  induction n with
  | zero =>
    have e : (0 : ℕ) + 1 = 1 := rfl
    rw [e]
    simp only [pow_one, Nat.fib_zero, Nat.fib_one, Nat.fib_two, Nat.cast_zero,
      Nat.cast_one, zero_add, mul_one]
    module
  | succ n ih =>
    have hS2 : (!![0, 5; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ 2
      = 5 • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := wanted_S_sq_smul p
    have hpow : ((1 : Matrix (Fin 2) (Fin 2) (ZMod p)) + !![0, 5; 1, 0]) ^ ((n + 1) + 1)
      = ((1 : Matrix (Fin 2) (Fin 2) (ZMod p)) + !![0, 5; 1, 0])
        * (((1 : Matrix (Fin 2) (Fin 2) (ZMod p)) + !![0, 5; 1, 0]) ^ (n + 1)) := by
      rw [pow_succ']
    have hE : (n + 1) + 1 + 1 = n + 3 := by omega
    have hP : (n + 1) + 1 = n + 2 := by omega
    rw [hpow, ← mul_smul_comm, ih]
    have hD := wanted_double_mul p
      (2 ^ (n + 1) * ((Nat.fib n : ZMod p) + (Nat.fib (n + 2) : ZMod p)))
      (2 ^ (n + 1) * (Nat.fib (n + 1) : ZMod p))
      !![0, 5; 1, 0] hS2
    rw [hD]
    have hA : 2 ^ (n + 1) * ((Nat.fib n : ZMod p) + (Nat.fib (n + 2) : ZMod p))
      + 5 * (2 ^ (n + 1) * (Nat.fib (n + 1) : ZMod p))
      = 2 ^ ((n + 1) + 1)
        * ((Nat.fib (n + 1) : ZMod p) + (Nat.fib ((n + 1) + 2) : ZMod p)) := by
      have hH := wanted_half_add5 p n
      have hF : 2 ^ (n + 1)
        * (((Nat.fib n : ZMod p) + (Nat.fib (n + 2) : ZMod p))
          + 5 * (Nat.fib (n + 1) : ZMod p))
        = 2 ^ (n + 1)
          * (2 * ((Nat.fib (n + 1) : ZMod p) + (Nat.fib (n + 3) : ZMod p))) := by
        rw [hH]
      have hL : 2 ^ (n + 1) * ((Nat.fib n : ZMod p) + (Nat.fib (n + 2) : ZMod p))
        + 5 * (2 ^ (n + 1) * (Nat.fib (n + 1) : ZMod p))
        = 2 ^ (n + 1)
          * (((Nat.fib n : ZMod p) + (Nat.fib (n + 2) : ZMod p))
            + 5 * (Nat.fib (n + 1) : ZMod p)) := by
        ring
      have hQ : (n + 1) + 2 = n + 3 := by omega
      rw [hL, hF, hQ]
      have hE2 : (n + 1) + 1 = n + 2 := by omega
      have hP2 : (2 : ZMod p) ^ ((n + 1) + 1) = 2 ^ (n + 1) * 2 := by
        rw [hE2, pow_succ]
      rw [hP2]
      ring
    have hB : 2 ^ (n + 1) * ((Nat.fib n : ZMod p) + (Nat.fib (n + 2) : ZMod p))
      + 2 ^ (n + 1) * (Nat.fib (n + 1) : ZMod p)
      = 2 ^ ((n + 1) + 1) * (Nat.fib ((n + 1) + 1) : ZMod p) := by
      have hH := wanted_half_add p n
      have hF : 2 ^ (n + 1)
        * (((Nat.fib n : ZMod p) + (Nat.fib (n + 2) : ZMod p))
          + (Nat.fib (n + 1) : ZMod p))
        = 2 ^ (n + 1) * (2 * (Nat.fib (n + 2) : ZMod p)) := by
        rw [hH]
      have hL : 2 ^ (n + 1) * ((Nat.fib n : ZMod p) + (Nat.fib (n + 2) : ZMod p))
        + 2 ^ (n + 1) * (Nat.fib (n + 1) : ZMod p)
        = 2 ^ (n + 1)
          * (((Nat.fib n : ZMod p) + (Nat.fib (n + 2) : ZMod p))
            + (Nat.fib (n + 1) : ZMod p)) := by
        ring
      rw [hL, hF, hP]
      have hP2 : (2 : ZMod p) ^ ((n + 1) + 1) = 2 ^ (n + 1) * 2 := by
        rw [hP, pow_succ]
      rw [hP2]
      ring
    rw [hE] at hA
    rw [hP] at hB
    rw [hA, hB]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wanted_two_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma wanted_two_ne_zero (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
  (2 : ZMod p) ≠ 0 := by
  have hp : Nat.Prime p := Fact.out
  have h2lt : 2 < p := by
    have h := hp.two_le
    omega
  have hC : (((2 : ℕ) : ZMod p)) ≠ 0 := by
    intro hD
    rw [ZMod.natCast_eq_zero_iff] at hD
    have hle := Nat.le_of_dvd (by norm_num) hD
    omega
  simpa using hC

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wanted_fib_two_mul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma wanted_fib_two_mul_eq (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
  (Nat.fib (2 * p) : ZMod p) = (5 : ZMod p) ^ (p / 2) := by
  have hp : Nat.Prime p := Fact.out
  have h2ne : (2 : ZMod p) ≠ 0 := wanted_two_ne_zero p hp2
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hmod2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  have hm : p = 2 * (p / 2) + 1 := by omega
  have hP1 : p - 1 + 1 = p := by
    have h := hp.two_le
    omega
  -- S and T abbreviations as explicit terms
  set S : Matrix (Fin 2) (Fin 2) (ZMod p) := !![0, 5; 1, 0] with hSdef
  set T : Matrix (Fin 2) (Fin 2) (ZMod p) := 1 + !![0, 5; 1, 0] with hTdef
  -- Freshman: T^p = 1 + S^p
  have hC : Commute (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) S := Commute.one_left S
  have hFro : T ^ p = 1 + S ^ p := by
    rw [hTdef]
    have h := add_pow_char_pow_of_commute (R := Matrix (Fin 2) (Fin 2) (ZMod p)) p 1 hC
    simpa [pow_one] using h
  -- S^p explicit via odd power
  have hSp0 := wanted_S_odd_pow p (p / 2)
  rw [← hm] at hSp0
  -- T^p explicit
  have hTexp : T ^ p
    = !![(1 : ZMod p), (5 : ZMod p) ^ (p / 2 + 1); (5 : ZMod p) ^ (p / 2), 1] := by
    rw [hFro, hSp0, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.add_apply, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one, add_zero, zero_add] <;>
      ring
  -- 2 • T^p explicit
  have h2T : (2 : ZMod p) • T ^ p
    = !![(2 : ZMod p), 2 * (5 : ZMod p) ^ (p / 2 + 1);
      2 * (5 : ZMod p) ^ (p / 2), 2] := by
    rw [hTexp]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one, smul_eq_mul] <;>
      ring
  -- T_double at n = p-1
  have hTD0 := wanted_T_double p (p - 1)
  have hPm1 : (p - 1) + 1 = p := hP1
  have hPm2 : (p - 1) + 2 = p + 1 := by
    have h := hp.two_le
    omega
  rw [hPm1] at hTD0
  rw [hPm2] at hTD0
  -- hTD0 : 2 • T^p = (2^p * (F_{p-1} + F_{p+1})) • 1 + (2^p * F_p) • S
  -- convert RHS to explicit matrix
  have hCS : ((2 : ZMod p) ^ p * ((Nat.fib (p - 1) : ZMod p) + (Nat.fib (p + 1) : ZMod p)))
    • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))
    + ((2 : ZMod p) ^ p * (Nat.fib p : ZMod p)) • S
    = !![(2 : ZMod p) ^ p * ((Nat.fib (p - 1) : ZMod p) + (Nat.fib (p + 1) : ZMod p)),
      5 * ((2 : ZMod p) ^ p * (Nat.fib p : ZMod p));
      (2 : ZMod p) ^ p * (Nat.fib p : ZMod p),
      (2 : ZMod p) ^ p * ((Nat.fib (p - 1) : ZMod p) + (Nat.fib (p + 1) : ZMod p))] := by
    rw [hSdef, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one,
        smul_eq_mul] <;>
      ring
  rw [hCS] at hTD0
  -- compare (0,0) entries: 2^p * L = 2
  have hc : (2 : ZMod p) ^ p * ((Nat.fib (p - 1) : ZMod p) + (Nat.fib (p + 1) : ZMod p))
    = 2 := by
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod p) => M 0 0) (hTD0.symm.trans h2T)
    simpa only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.mk_zero, Fin.mk_one] using h00
  -- compare (1,0) entries: 2^p * F = 2 * 5^m
  have hd : (2 : ZMod p) ^ p * (Nat.fib p : ZMod p) = 2 * (5 : ZMod p) ^ (p / 2) := by
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod p) => M 1 0) (hTD0.symm.trans h2T)
    simpa only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.mk_zero, Fin.mk_one] using h10
  -- cancel 2^p = 2
  have h2p : (2 : ZMod p) ^ p = 2 := ZMod.pow_card 2
  rw [h2p] at hc hd
  have hL : (Nat.fib (p - 1) : ZMod p) + (Nat.fib (p + 1) : ZMod p) = 1 := by
    have hcc : (2 : ZMod p) * (((Nat.fib (p - 1) : ZMod p) + (Nat.fib (p + 1) : ZMod p))) = 2 * 1 := by
      rwa [mul_one]
    exact mul_left_cancel₀ h2ne hcc
  have hF : (Nat.fib p : ZMod p) = (5 : ZMod p) ^ (p / 2) := by
    exact mul_left_cancel₀ h2ne hd
  -- F_{2p} via addition formula
  have h2peq : 2 * p = p + (p - 1) + 1 := by
    have h := hp.two_le
    omega
  have hF2p : Nat.fib (2 * p)
    = Nat.fib p * Nat.fib (p - 1) + Nat.fib (p + 1) * Nat.fib p := by
    rw [h2peq, Nat.fib_add, hP1]
  rw [hF2p]
  push_cast
  have hFac : (Nat.fib p : ZMod p) * (Nat.fib (p - 1) : ZMod p)
    + (Nat.fib (p + 1) : ZMod p) * (Nat.fib p : ZMod p)
    = (Nat.fib p : ZMod p)
      * ((Nat.fib (p - 1) : ZMod p) + (Nat.fib (p + 1) : ZMod p)) := by
    ring
  rw [hFac, hL, hF, mul_one]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wanted_fib_mod5_period](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma wanted_fib_mod5_period (n : ℕ) :
  Nat.fib (n + 20) % 5 = Nat.fib n % 5 := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih1 ih2 =>
    have e1 : (n + 2) + 20 = (n + 20) + 2 := by omega
    have e2 : (n + 20) + 1 = (n + 1) + 20 := by omega
    have f1 : Nat.fib ((n + 20) + 2) = Nat.fib (n + 20) + Nat.fib ((n + 20) + 1) :=
      Nat.fib_add_two
    have f2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    rw [e1, f1, e2, f2]
    conv_lhs => rw [Nat.add_mod]
    conv_rhs => rw [Nat.add_mod]
    rw [ih1, ih2]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wanted_fib_mod5_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma wanted_fib_mod5_mul (k r : ℕ) :
  Nat.fib (20 * k + r) % 5 = Nat.fib r % 5 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : 20 * (k + 1) + r = (20 * k + r) + 20 := by ring
    rw [e, wanted_fib_mod5_period, ih]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wanted_fib_mod2_period](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma wanted_fib_mod2_period (n : ℕ) :
  Nat.fib (n + 3) % 2 = Nat.fib n % 2 := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih1 ih2 =>
    have e1 : (n + 2) + 3 = (n + 3) + 2 := by omega
    have e2 : (n + 3) + 1 = (n + 1) + 3 := by omega
    have f1 : Nat.fib ((n + 3) + 2) = Nat.fib (n + 3) + Nat.fib ((n + 3) + 1) :=
      Nat.fib_add_two
    have f2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    rw [e1, f1, e2, f2]
    conv_lhs => rw [Nat.add_mod]
    conv_rhs => rw [Nat.add_mod]
    rw [ih1, ih2]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wanted_fib_mod2_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma wanted_fib_mod2_mul (k r : ℕ) :
  Nat.fib (3 * k + r) % 2 = Nat.fib r % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : 3 * (k + 1) + r = (3 * k + r) + 3 := by ring
    rw [e, wanted_fib_mod2_period, ih]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wanted_fib_two_mul_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma wanted_fib_two_mul_odd (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≠ 3) :
  Odd (Nat.fib (2 * p)) := by
  have hp3dvd : ¬ (3 ∣ 2 * p) := by
    intro hD
    have hprime : Nat.Prime 3 := by decide
    rw [hprime.dvd_mul] at hD
    obtain h | h := hD
    · norm_num at h
    · have hEq := hp.eq_one_or_self_of_dvd 3 h
      obtain h1 | h1 <;> omega := hEq
  have hmod : (2 * p) % 3 = 1 ∨ (2 * p) % 3 = 2 := by omega
  have hdecomp : 2 * p = 3 * (2 * p / 3) + (2 * p) % 3 := (Nat.div_add_mod (2 * p) 3).symm
  rw [Nat.odd_iff, hdecomp, wanted_fib_mod2_mul]
  obtain h | h <;> rw [h] <;> decide := hmod

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wanted_fib_mod5_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma wanted_fib_mod5_eq (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 < p) :
  Nat.fib (2 * p) % 5 = p % 5 := by
  have hp2 : p ≠ 2 := by omega
  have h2 : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have h5 : p % 5 ≠ 0 := by
    intro h0
    have hD : 5 ∣ p := Nat.dvd_of_mod_eq_zero h0
    have hEq := hp.eq_one_or_self_of_dvd 5 hD
    obtain h1 | h1 <;> omega := hEq
  have hlt10 : p % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have h10 : p % 10 = 1 ∨ p % 10 = 3 ∨ p % 10 = 7 ∨ p % 10 = 9 := by omega
  have h2p20 : (2 * p) % 20 = 2 * (p % 10) := by omega
  have hdecomp : 2 * p = 20 * (2 * p / 20) + (2 * p) % 20 := (Nat.div_add_mod (2 * p) 20).symm
  have hF : Nat.fib (2 * p) % 5 = Nat.fib ((2 * p) % 20) % 5 := by
    conv_lhs => rw [hdecomp]
    rw [wanted_fib_mod5_mul]
  rw [hF, h2p20]
  have hp5v : p % 5 = (p % 10) % 5 := by omega
  rw [hp5v]
  obtain h | h | h | h <;> rw [h] <;> decide := h10

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wanted_jacobi_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma wanted_jacobi_eq (p : ℕ) [Fact (Nat.Prime p)] (hp5 : 5 < p) :
  jacobiSym 5 (Nat.fib (2 * p)) = legendreSym p 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp : Nat.Prime p := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hOddF : Odd (Nat.fib (2 * p)) := wanted_fib_two_mul_odd p hp hp3
  have hF5 : Nat.fib (2 * p) % 5 = p % 5 :=
    wanted_fib_mod5_eq p hp hp5
  -- Step 1: jacobiSym 5 F = jacobiSym F 5 (reciprocity, 5 ≡ 1 mod 4)
  have hRecJ : jacobiSym 5 (Nat.fib (2 * p)) = jacobiSym (Nat.fib (2 * p) : ℤ) 5 := by
    have h := jacobiSym.quadratic_reciprocity_one_mod_four (a := 5)
      (b := Nat.fib (2 * p)) (by decide) hOddF
    simpa using h
  -- Step 2: legendreSym p 5 = legendreSym 5 p (reciprocity)
  have hRecL : legendreSym p 5 = legendreSym 5 (p : ℤ) := by
    have h := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p)
      (by decide) hp2
    simpa using h
  -- Step 3: legendreSym 5 p = jacobiSym p 5 (prime denominator)
  have hToJ : legendreSym 5 (p : ℤ) = jacobiSym (p : ℤ) 5 :=
    jacobiSym.legendreSym.to_jacobiSym 5 (p : ℤ)
  -- Step 4: the two Jacobi values agree (same residue mod 5)
  have hModEq : (Nat.fib (2 * p) : ℤ) % ((5 : ℕ) : ℤ) = (p : ℤ) % ((5 : ℕ) : ℤ) := by
    have e1 : (((Nat.fib (2 * p) % 5 : ℕ)) : ℤ)
      = (Nat.fib (2 * p) : ℤ) % (((5 : ℕ)) : ℤ) := Int.natCast_emod _ _
    have e2 : (((p % 5 : ℕ)) : ℤ)
      = (p : ℤ) % (((5 : ℕ)) : ℤ) := Int.natCast_emod _ _
    rw [← e1, ← e2, hF5]
  have hJeq : jacobiSym (Nat.fib (2 * p) : ℤ) 5 = jacobiSym (p : ℤ) 5 :=
    jacobiSym.mod_left' hModEq
  rw [hRecJ, hJeq, ← hToJ, ← hRecL]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wanted_mem_core](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma wanted_mem_core (p : ℕ) [Fact (Nat.Prime p)] (hp5 : 5 < p) :
  (Nat.fib (2 * p))
    ∣ Nat.fib (Int.toNat (((Nat.fib (2 * p)) : ℤ) - jacobiSym 5 (Nat.fib (2 * p))))
  ∧ ¬(Nat.fib (2 * p)).Prime ∧ 1 < Nat.fib (2 * p) := by
  have hp : Nat.Prime p := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  set F : ℕ := Nat.fib (2 * p) with hFdef
  set j : ℤ := jacobiSym 5 (Nat.fib (2 * p)) with hjdef
  have hOddF : Odd F := wanted_fib_two_mul_odd p hp hp3
  -- mod-p equality in ZMod
  have hFibEq : (F : ZMod p) = (5 : ZMod p) ^ (p / 2) := by
    rw [hFdef]
    exact wanted_fib_two_mul_eq p hp2
  have hEuler : (((legendreSym p 5 : ℤ)) : ZMod p) = (5 : ZMod p) ^ (p / 2) := by
    simpa using legendreSym.eq_pow p 5
  have hJL : j = legendreSym p 5 := by
    rw [hjdef]
    exact wanted_jacobi_eq p hp5
  have hZMod : (F : ZMod p) = ((j : ℤ) : ZMod p) := by
    rw [hJL, hEuler, hFibEq]
  -- divisibility by p (integers)
  have hpZ : (p : ℤ) ∣ ((F : ℤ) - j) := by
    have h1 : (((F : ℕ) : ℤ) : ZMod p) = ((j : ℤ) : ZMod p) := by
      simpa using hZMod
    rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd] at h1
    have h3 : j - ((F : ℕ) : ℤ) = -(((F : ℕ) : ℤ) - j) := by ring
    have hFcast : ((F : ℕ) : ℤ) = ((F : ℤ)) := rfl
    rw [hFcast] at h1 h3
    rwa [h3, dvd_neg] at h1
  -- j is odd (hence F - j is even)
  have hj0 : j ≠ 0 := by
    rw [hJL]
    intro h0
    rw [legendreSym.eq_zero_iff] at h0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    have hND : ¬ ((p : ℕ) : ℤ) ∣ (5 : ℤ) := by
      intro hD
      have hD' : p ∣ 5 := by exact_mod_cast hD
      have hle := Nat.le_of_dvd (by norm_num) hD'
      omega
    exact hND h0
  have hOddJ : Odd j := by
    have hjTri : j = 0 ∨ j = 1 ∨ j = -1 := by
      rw [hjdef]
      exact jacobiSym.trichotomy _ _
    obtain h0 | h1 | hm1 := hjTri
    · exact absurd h0 hj0
    · rw [h1]; exact odd_one
    · rw [hm1]; exact odd_neg_one
  have hEven : Even (((F : ℤ)) - j) :=
    ((Int.odd_coe_nat F).mpr hOddF).sub_odd hOddJ
  have h2Z : (2 : ℤ) ∣ (((F : ℤ)) - j) := even_iff_two_dvd.mp hEven
  -- bounds and compositeness inputs
  have h6p : 6 ≤ p := by omega
  have hFib6 : Nat.fib 6 = 8 := by decide
  have hMono := Nat.fib_mono h6p
  rw [hFib6] at hMono
  have h1Fp : 1 < Nat.fib p := by omega
  have hplt : p < 2 * p := by
    have hpos : 0 < p := hp.pos
    omega
  have hFplt : Nat.fib p < Nat.fib (2 * p) :=
    (Nat.fib_lt_fib (show 2 ≤ p by omega)).mpr hplt
  have hDvdFp : Nat.fib p ∣ Nat.fib (2 * p) :=
    Nat.isDvdSequence_fib p (2 * p) (dvd_mul_left p 2)
  have hNotPrime : ¬(Nat.fib (2 * p)).Prime :=
    Nat.not_prime_of_dvd_of_lt hDvdFp (by omega) hFplt
  have h1F : 1 < F := by
    rw [hFdef]
    omega
  -- nonnegativity of F - j
  have hj1 : j ≤ 1 := by
    have hjTri : j = 0 ∨ j = 1 ∨ j = -1 := by
      rw [hjdef]
      exact jacobiSym.trichotomy _ _
    obtain h0 | h1 | hm1 <;> omega := hjTri
  have hXnn : 0 ≤ (((F : ℤ)) - j) := by
    have h1Fc : ((1 : ℕ) : ℤ) ≤ ((F : ℕ) : ℤ) := by
      exact_mod_cast le_of_lt h1F
    have hFF : ((F : ℕ) : ℤ) = ((F : ℤ)) := rfl
    omega
  -- transfer divisibilities to ℕ for toNat
  have h2N : 2 ∣ Int.toNat ((((F : ℤ)) - j)) := by
    have e2 : ((2 : ℤ)) = ((((2 : ℕ))) : ℤ) := by norm_num
    have eX : ((((F : ℤ)) - j)) = (((Int.toNat ((((F : ℤ)) - j)) : ℕ)) : ℤ) :=
      (Int.toNat_of_nonneg hXnn).symm
    rwa [e2, eX, Int.natCast_dvd_natCast] at h2Z
  have hpN : p ∣ Int.toNat ((((F : ℤ)) - j)) := by
    have ep : ((p : ℤ)) = ((((p : ℕ))) : ℤ) := by norm_num
    have eX : ((((F : ℤ)) - j)) = (((Int.toNat ((((F : ℤ)) - j)) : ℕ)) : ℤ) :=
      (Int.toNat_of_nonneg hXnn).symm
    rwa [ep, eX, Int.natCast_dvd_natCast] at hpZ
  have hCop : Nat.Coprime 2 p :=
    (Nat.coprime_primes (by decide : Nat.Prime 2) hp).mpr (by omega)
  have h2pN : 2 * p ∣ Int.toNat ((((F : ℤ)) - j)) :=
    hCop.mul_dvd_of_dvd_of_dvd h2N hpN
  -- Fibonacci divisibility
  have hFibDvd : F ∣ Nat.fib (Int.toNat ((((F : ℤ)) - j))) := by
    rw [hFdef]
    exact Nat.isDvdSequence_fib (2 * p) _ h2pN
  -- reassemble (fold explicit haves to match)
  rw [← hFdef] at hNotPrime
  exact ⟨hFibDvd, hNotPrime, h1F⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[infinitely_many_primes_fibonacci_pseudoprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
lemma infinitely_many_primes_fibonacci_pseudoprime
  :
-- imply
  Set.Infinite {p : ℕ | p.Prime ∧
    let n := by
-- proof
  have hSub : {p : ℕ | p.Prime ∧ 5 < p}
    ⊆ {p : ℕ | p.Prime ∧
      let n := Nat.fib (2 * p)
      n ∣ Nat.fib (Int.toNat ((n : ℤ) - jacobiSym 5 n)) ∧ ¬n.Prime ∧ 1 < n} := by
    intro p hp
    obtain ⟨hPrime, h5⟩ := hp
    haveI : Fact (Nat.Prime p) := ⟨hPrime⟩
    have hCore := wanted_mem_core p h5
    show p.Prime ∧
      (let n := Nat.fib (2 * p)
      n ∣ Nat.fib (Int.toNat ((n : ℤ) - jacobiSym 5 n)) ∧ ¬n.Prime ∧ 1 < n)
    exact ⟨hPrime, hCore.1, hCore.2.1, hCore.2.2⟩
  have hInf : {p : ℕ | p.Prime ∧ 5 < p}.Infinite := by
    have hEq : {p : ℕ | p.Prime ∧ 5 < p} = {p : ℕ | p.Prime} \ Set.Iic 5 := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_Iic, not_le]
    rw [hEq]
    exact Nat.infinite_setOfPred_prime.sdiff (Set.finite_Iic 5)
  exact Set.Infinite.mono hSub hInf

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
