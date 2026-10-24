import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.FiniteFieldArith
open Polynomial FiniteFieldArith LongDivision
open Classical


namespace FiniteFieldArith

/--
[fq_add_cost_is_sum_over_coefficients](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma fq_add_cost_is_sum_over_coefficients
  {p d : ℕ} :
-- imply
  ∑ _i : Fin d, fpAddBitOps p = fqAddBitOps p d := by
-- proof
  simp only [fqAddBitOps, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end FiniteFieldArith

namespace FiniteFieldArith

/--
[fqAddBitOps_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma fqAddBitOps_def
  {p d : ℕ} :
-- imply
  fqAddBitOps p d = d * (3 * (Nat.log 2 p + 1)) := by
-- proof
  unfold fqAddBitOps fpAddBitOps bitSize; ring

end FiniteFieldArith

namespace FiniteFieldArith

/--
[d_mul_log_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma d_mul_log_le
  {p d : ℕ}
-- given
  (hp : 2 ≤ p) :
-- imply
  d * Nat.log 2 p ≤ Nat.log 2 (p ^ d) := by
-- proof
  have hle : 2 ^ Nat.log 2 p ≤ p := Nat.pow_log_le_self 2 (by omega : p ≠ 0)
  calc d * Nat.log 2 p
    = Nat.log 2 (2 ^ (d * Nat.log 2 p)) := by rw [Nat.log_pow (by norm_num : 1 < 2)]
    _ ≤ Nat.log 2 (p ^ d) := by
      apply Nat.log_mono_right
      calc 2 ^ (d * Nat.log 2 p) = (2 ^ Nat.log 2 p) ^ d := by ring
        _ ≤ p ^ d := Nat.pow_le_pow_left hle d

end FiniteFieldArith

namespace FiniteFieldArith

/--
[d_le_log_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma d_le_log_pow
  {p d : ℕ}
-- given
  (hp : 2 ≤ p) :
-- imply
  d ≤ Nat.log 2 (p ^ d) := by
-- proof
  calc d = Nat.log 2 (2 ^ d) := by rw [Nat.log_pow (by norm_num : 1 < 2)]
    _ ≤ Nat.log 2 (p ^ d) := Nat.log_mono_right (Nat.pow_le_pow_left hp d)

end FiniteFieldArith

namespace FiniteFieldArith

/--
[d_mul_bitSize_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma d_mul_bitSize_le
  {p d : ℕ}
-- given
  (hp : 2 ≤ p) :
-- imply
  d * bitSize p ≤ 2 * bitSize (p ^ d) := by
-- proof
  unfold bitSize
  have h1 := d_mul_log_le p d hp
  have h2 := d_le_log_pow p d hp
  have h3 : d * (Nat.log 2 p + 1) = d * Nat.log 2 p + d := by ring
  rw [h3]; linarith

end FiniteFieldArith

namespace FiniteFieldArith

/--
[fq_add_bitOps_linear](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma fq_add_bitOps_linear
  {p d : ℕ}
-- given
  (hp : Nat.Prime p) :
-- imply
  fqAddBitOps p d ≤ 6 * bitSize (p ^ d) := by
-- proof
  unfold fqAddBitOps fpAddBitOps
  have h := d_mul_bitSize_le p d hp.two_le
  nlinarith

end FiniteFieldArith

namespace FiniteFieldArith

/--
[fq_sub_bitOps_linear](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma fq_sub_bitOps_linear
  {p d : ℕ}
-- given
  (hp : Nat.Prime p) :
-- imply
  fqSubBitOps p d ≤ 6 * bitSize (p ^ d) :=
-- proof
  fq_add_bitOps_linear p d hp

end FiniteFieldArith

namespace FiniteFieldArith

/--
[fq_add_complexity_linear](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma fq_add_complexity_linear
-- imply
  ∃ C : ℕ, ∀ (p : ℕ) (d : ℕ), Nat.Prime p → fqAddBitOps p d ≤ C * bitSize (p ^ d) :=
-- proof
  ⟨6, fun p d hp => fq_add_bitOps_linear p d hp⟩
end FiniteFieldArith
open Polynomial


/--
[DFT_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma DFT_apply
  [CommRing R]
  {ω : R}
  {n : ℕ}
  {f : R[X]}
  {i : Fin n} :
-- imply
  DFT ω n f i = f.eval (ω ^ i.val) :=
-- proof
  rfl

/--
[cyclicConv_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma cyclicConv_def
  [CommRing R]
  {n : ℕ}
  {f g : R[X]} :
-- imply
  cyclicConv n f g = (f * g) %ₘ (X ^ n - 1) :=
-- proof
  rfl

/--
[eval_modByMonic_eq_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma eval_modByMonic_eq_eval
  [CommRing R]
  {p m : R[X]}
  {a : R}
-- given
  (hroot : m.IsRoot a) :
-- imply
  (p %ₘ m).eval a = p.eval a := by
-- proof
  conv_rhs => rw [← modByMonic_add_div p m]
  simp only [eval_add, eval_mul]
  rw [IsRoot.def.mp hroot, zero_mul, add_zero]

/--
[isRoot_X_pow_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma isRoot_X_pow_sub_one
  [CommRing R]
  {ω : R}
  {n : ℕ}
  {i : ℕ}
-- given
  (hω : ω ^ n = 1) :
-- imply
  (X ^ n - 1 : R[X]).IsRoot (ω ^ i) := by
-- proof
  simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_one]
  rw [← pow_mul, mul_comm, pow_mul, hω, one_pow, sub_self]

/--
[dft_cyclicConv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma dft_cyclicConv
  [CommRing R]
  {ω : R}
  {n : ℕ}
  {f g : R[X]}
-- given
  (hω : ω ^ n = 1) :
-- imply
  DFT ω n (cyclicConv n f g) = DFT ω n f * DFT ω n g := by
-- proof
  ext i
  simp only [DFT_apply, Pi.mul_apply, cyclicConv]
  rwa [eval_modByMonic_eq_eval _ _ _ (isRoot_X_pow_sub_one hω i.val)]

/--
[isPrim2PowRoot_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma isPrim2PowRoot_sq
  [CommRing R]
  {ω : R}
-- given
  (h : IsPrim2PowRoot ω (n + 1)) :
-- imply
  IsPrim2PowRoot (ω ^ 2) n := by
-- proof
  cases n with
  | zero => trivial
  | succ n =>
    show (ω ^ 2) ^ 2 ^ n = -1
    rwa [← pow_mul, show 2 * 2 ^ n = 2 ^ (n + 1) from by ring]

/--
[isPrim2PowRoot_pow_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma isPrim2PowRoot_pow_eq_one
  [CommRing R]
  {ω : R}
-- given
  (h : IsPrim2PowRoot ω (n + 1)) :
-- imply
  ω ^ 2 ^ (n + 1) = 1 := by
-- proof
  rw [show (2:ℕ) ^ (n + 1) = 2 ^ n * 2 from by ring, pow_mul, h]; norm_num

/--
[natDegree_sum_C_X_pow_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma natDegree_sum_C_X_pow_lt
  [CommRing R]
  {m : ℕ}
  {c : ℕ → R}
-- given
  (hm : 0 < m) :
-- imply
  (∑ j ∈ Finset.range m, C (c j) * X ^ j).natDegree < m :=
-- proof
  calc _ ≤ (Finset.range m).sup (fun j => (C (c j) * X ^ j).natDegree) :=
    natDegree_sum_le _ _
    _ ≤ (Finset.range m).sup id :=
      Finset.sup_mono_fun (fun j _ => natDegree_C_mul_X_pow_le (c j) j)
    _ < m := by
      rw [Finset.sup_lt_iff (by omega)]
      intro j hj; exact Finset.mem_range.mp hj

/--
[fftTwistedDiff_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma fftTwistedDiff_eval
  [CommRing R]
  {ω : R}
  {m : ℕ}
  {f : R[X]}
  {x : R} :
-- imply
  (fftTwistedDiff ω m f).eval x = (polyFirstHalf m f - polySecondHalf m f).eval (ω * x) := by
-- proof
  simp only [fftTwistedDiff, polyFirstHalf, polySecondHalf,
    eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, eval_sub, mul_pow]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _; ring

/--
[poly_split_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma poly_split_eval
  [CommRing R]
  {m : ℕ}
  {f : R[X]}
  {x : R}
-- given
  (hf : f.natDegree < 2 * m) :
-- imply
  f.eval x = (polyFirstHalf m f).eval x + x ^ m * (polySecondHalf m f).eval x := by
-- proof
  rw [eval_eq_sum_range' hf]
  simp only [polyFirstHalf, polySecondHalf, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  rw [show 2 * m = m + m from by ring, Finset.sum_range_add, Finset.mul_sum]
  congr 1; apply Finset.sum_congr rfl; intro j _; rw [pow_add]; ring

/--
[fft_even_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma fft_even_identity
  [CommRing R]
  {ω : R}
  {m : ℕ}
  {f : R[X]}
  {i : ℕ}
-- given
  (hf : f.natDegree < 2 * m)
  (hω : ω ^ (2 * m) = 1) :
-- imply
  f.eval (ω ^ (2 * i)) = (polyFirstHalf m f + polySecondHalf m f).eval ((ω ^ 2) ^ i) := by
-- proof
  rw [show ω ^ (2 * i) = (ω ^ 2) ^ i from pow_mul ω 2 i,
    poly_split_eval m f hf, eval_add]
  have key : ((ω ^ 2) ^ i) ^ m = 1 := by
    calc ((ω ^ 2) ^ i) ^ m = ω ^ (2 * (i * m)) := by rw [← pow_mul, ← pow_mul]
      _ = ω ^ (2 * m * i) := by congr 1; ring
      _ = (ω ^ (2 * m)) ^ i := pow_mul ω (2 * m) i
      _ = 1 := by rw [hω, one_pow]
  rw [key, one_mul]

/--
[fft_odd_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma fft_odd_identity
  [CommRing R]
  {ω : R}
  {m : ℕ}
  {f : R[X]}
  {i : ℕ}
-- given
  (hf : f.natDegree < 2 * m)
  (hωm : ω ^ m = -1) :
-- imply
  f.eval (ω ^ (2 * i + 1)) = (fftTwistedDiff ω m f).eval ((ω ^ 2) ^ i) := by
-- proof
  rw [poly_split_eval m f hf]
  have hpow_odd_m : (ω ^ (2 * i + 1)) ^ m = -1 := by
    calc (ω ^ (2 * i + 1)) ^ m = ω ^ ((2 * i + 1) * m) := (pow_mul _ _ _).symm
      _ = ω ^ (m * (2 * i) + m) := by congr 1; ring
      _ = ω ^ (m * (2 * i)) * ω ^ m := pow_add ω _ m
      _ = (ω ^ m) ^ (2 * i) * ω ^ m := by rw [pow_mul]
      _ = (-1) ^ (2 * i) * (-1) := by rw [hωm]
      _ = -1 := by simp [pow_mul]
  rw [hpow_odd_m, neg_one_mul, ← sub_eq_add_neg, ← eval_sub]
  rw [show ω ^ (2 * i + 1) = ω * (ω ^ 2) ^ i from by
    rw [show 2 * i + 1 = 1 + 2 * i from by ring, pow_add, pow_one, pow_mul]]
  rw [← fftTwistedDiff_eval]

/--
[fft_eq_DFT](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma fft_eq_DFT
  [CommRing R]
  {ω : R}
  {n : ℕ}
  {f : R[X]}
-- given
  (hprim : IsPrim2PowRoot ω n)
  (hdeg : f.natDegree < 2 ^ n) :
-- imply
  fft ω n f = DFT ω (2 ^ n) f := by
-- proof
  induction n generalizing ω f with
  | zero =>
    ext ⟨i, hi⟩; simp only [fft, DFT_apply]
    have : i = 0 := by omega
    subst this; simp
  | succ n ih =>
    ext ⟨k, hk⟩; simp only [fft, DFT_apply]
    set m := 2 ^ n
    set r := polyFirstHalf m f + polySecondHalf m f
    set s := fftTwistedDiff ω m f
    have hprim2 : IsPrim2PowRoot (ω ^ 2) n := isPrim2PowRoot_sq hprim
    have hm_pos : 0 < m := Nat.pos_of_ne_zero (by positivity)
    have hdeg_2m : f.natDegree < 2 * m := by
      rwa [show 2 * m = 2 ^ (n + 1) from by simp [m, pow_succ, mul_comm]]
    have hdeg_r : r.natDegree < 2 ^ n := by
      calc r.natDegree
        ≤ max (polyFirstHalf m f).natDegree (polySecondHalf m f).natDegree :=
          natDegree_add_le _ _
        _ < m := by
          simp only [Nat.max_lt]
          exact ⟨natDegree_sum_C_X_pow_lt hm_pos _, natDegree_sum_C_X_pow_lt hm_pos _⟩
    have hdeg_s : s.natDegree < 2 ^ n := natDegree_sum_C_X_pow_lt hm_pos _
    have hω2m : ω ^ (2 * m) = 1 := by
      rw [show 2 * m = 2 ^ (n + 1) from by simp [m, pow_succ, mul_comm]]
      exact isPrim2PowRoot_pow_eq_one hprim
    by_cases hmod : k % 2 = 0
    ·
      simp only [hmod, ↓reduceIte]
      have ih_r := congr_fun (ih (ω ^ 2) r hprim2 hdeg_r) ⟨k / 2, by omega⟩
      simp only [DFT_apply] at ih_r; rw [ih_r]
      conv_rhs => rw [show k = 2 * (k / 2) from by omega]
      exact (fft_even_identity ω m f hdeg_2m hω2m (k / 2)).symm
    ·
      simp only [hmod, ↓reduceIte]
      have ih_s := congr_fun (ih (ω ^ 2) s hprim2 hdeg_s) ⟨k / 2, by omega⟩
      simp only [DFT_apply] at ih_s; rw [ih_s]
      conv_rhs => rw [show k = 2 * (k / 2) + 1 from by omega]
      exact (fft_odd_identity ω m f hdeg_2m hprim (k / 2)).symm
section FFTPolyMulComplexity

/--
[fftPolyMulCost_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma fftPolyMulCost_le
  [CommRing R]
  {k : ℕ} :
-- imply
  fftPolyMulCost k ≤ 20 * 2 ^ k * (k + 1) := by
-- proof
  unfold fftPolyMulCost fftOpCount pointwiseMulOpCount computePowersOpCount scalarMulOpCount
  nlinarith [Nat.one_le_two_pow (n := k)]

/--
[cyclicConv_eq_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma cyclicConv_eq_mul
  [CommRing R]
  [Nontrivial R]
  {n : ℕ}
  {f g : R[X]}
-- given
  (hn : 0 < n)
  (hdeg : (f * g).natDegree < n) :
-- imply
  cyclicConv n f g = f * g := by
-- proof
  simp only [cyclicConv]
  rw [show (X : R[X]) ^ n - 1 = X ^ n - C 1 by simp,
    modByMonic_eq_self_iff (monic_X_pow_sub_C 1 (by omega)),
    degree_X_pow_sub_C (by omega : 0 < n)]
  exact degree_le_natDegree.trans_lt (by exact_mod_cast hdeg)

/--
[fft_poly_mul_complexity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma fft_poly_mul_complexity
  [CommRing R]
  {R : Type*}
  [CommRing R]
  {k : ℕ}
  {ω : R}
  {f g : R[X]}
-- given
  (hprim : IsPrim2PowRoot ω (k + 1))
  (hunit : IsUnit (2 : R))
  (hf : f.natDegree < 2 ^ k)
  (hg : g.natDegree < 2 ^ k) :
-- imply
  cyclicConv (2 ^ (k + 1)) f g = f * g ∧ DFT ω (2 ^ (k + 1)) (f * g) = DFT ω (2 ^ (k + 1)) f * DFT ω (2 ^ (k + 1)) g ∧ IsUnit ((2 : R) ^ (k + 1)) ∧ fftPolyMulCost (k + 1) ≤ 20 * 2 ^ (k + 1) * ((k + 1) + 1) := by
-- proof
  have hfg : (f * g).natDegree < 2 ^ (k + 1) :=
    calc (f * g).natDegree ≤ f.natDegree + g.natDegree := natDegree_mul_le
      _ < 2 ^ k + 2 ^ k := Nat.add_lt_add hf hg
      _ = 2 ^ (k + 1) := by ring
  obtain hR | hR := subsingleton_or_nontrivial R
  ·
    haveI : Subsingleton R[X] := inferInstance
    refine ⟨Subsingleton.elim _ _, ?_, ?_, ?_⟩
    · have : Subsingleton (Fin (2 ^ (k + 1)) → R) := inferInstance
      exact Subsingleton.elim _ _
    · rw [show (2 : R) ^ (k + 1) = 1 from Subsingleton.elim _ _]; exact isUnit_one
    · exact fftPolyMulCost_le (k + 1)
  ·
    have h1 : cyclicConv (2 ^ (k + 1)) f g = f * g :=
      cyclicConv_eq_mul (2 ^ (k + 1)) (by positivity) f g hfg
    refine ⟨h1, ?_, ?_, ?_⟩
    · rw [← h1]
      exact dft_cyclicConv ω (2 ^ (k + 1)) f g (isPrim2PowRoot_pow_eq_one hprim)
    · exact hunit.pow (k + 1)
    · exact fftPolyMulCost_le (k + 1)
end FFTPolyMulComplexity

namespace FiniteFieldArith

/--
[fp_repr_bitlength_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma fp_repr_bitlength_le
  [CommRing R]
  {intMulCost : ℕ → ℕ}
  {p : ℕ}
  [NeZero p]
  {a : ZMod p} :
-- imply
  bitlength a.val ≤ bitlength p := by
-- proof
  unfold bitlength
  exact Nat.size_le_size (le_of_lt (ZMod.val_lt a))

end FiniteFieldArith

namespace FiniteFieldArith

/--
[fp_mul_repr_bitlength_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma fp_mul_repr_bitlength_le
  [CommRing R]
  {intMulCost : ℕ → ℕ}
  {p : ℕ}
  [NeZero p]
  {a b : ZMod p} :
-- imply
  bitlength (a.val * b.val) ≤ 2 * bitlength p := by
-- proof
  unfold bitlength
  rw [Nat.size_le]
  have ha : a.val < p := ZMod.val_lt a
  have hb : b.val < p := ZMod.val_lt b
  have hp : p < 2 ^ Nat.size p := Nat.lt_size_self p
  have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  calc a.val * b.val
    < p * p := Nat.mul_lt_mul_of_le_of_lt (le_of_lt ha) hb hp0
    _ = p ^ 2 := by ring
    _ < (2 ^ Nat.size p) ^ 2 := Nat.pow_lt_pow_left hp (by norm_num)
    _ = 2 ^ (2 * Nat.size p) := by ring

end FiniteFieldArith

namespace FiniteFieldArith

/--
[modReductionCost_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma modReductionCost_le
  [CommRing R]
  {intMulCost : ℕ → ℕ}
  {n : ℕ}
-- given
  (hM_ge_id : ∀ n, n ≤ intMulCost n) :
-- imply
  modReductionCost intMulCost n ≤ 4 * intMulCost n := by
-- proof
  unfold modReductionCost
  have h := hM_ge_id n
  linarith

end FiniteFieldArith

namespace FiniteFieldArith

/--
[fp_mul_cost_is_O_intMulCost](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma fp_mul_cost_is_O_intMulCost
  [CommRing R]
  {intMulCost : ℕ → ℕ}
-- given
  (hM_ge_id : ∀ n, n ≤ intMulCost n) :
-- imply
  ∃ C : ℕ, ∀ p, fpMulCost intMulCost p ≤ C * intMulCost (bitlength p) := by
-- proof
  refine ⟨5, fun p => ?_⟩
  unfold fpMulCost
  have hred := modReductionCost_le intMulCost hM_ge_id (bitlength p)
  linarith

end FiniteFieldArith

namespace FiniteFieldArith

/--
[bitSize_pow_ge_e](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma bitSize_pow_ge_e
  [CommRing R]
  {intMulCost : ℕ → ℕ}
  {p e : ℕ}
-- given
  (hp : 2 ≤ p) :
-- imply
  e ≤ bitSize (p ^ e) := by
-- proof
  unfold bitSize
  calc e = Nat.log 2 (2 ^ e) := by rw [Nat.log_pow (by norm_num : 1 < 2)]
    _ ≤ Nat.log 2 (p ^ e) := Nat.log_mono_right (Nat.pow_le_pow_left hp e)
    _ ≤ Nat.log 2 (p ^ e) + 1 := Nat.le_succ _

end FiniteFieldArith

namespace FiniteFieldArith

/--
[fqInvCost_kb_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma fqInvCost_kb_le
  [CommRing R]
  {intMulCost : ℕ → ℕ}
  {p e K : ℕ}
-- given
  (hp : 2 ≤ p)
  (hlog : LogEBoundedByLogP K p e) :
-- imply
  e * (bitSize p + bitSize e) ≤ (2 * K + 5) * bitSize (p ^ e) := by
-- proof
  unfold bitSize LogEBoundedByLogP at *
  have h1 : e * Nat.log 2 p ≤ Nat.log 2 (p ^ e) := by
    have hle : 2 ^ Nat.log 2 p ≤ p := Nat.pow_log_le_self 2 (by omega : p ≠ 0)
    calc e * Nat.log 2 p
      = Nat.log 2 (2 ^ (e * Nat.log 2 p)) := by rw [Nat.log_pow (by norm_num : 1 < 2)]
      _ ≤ Nat.log 2 (p ^ e) := by
        apply Nat.log_mono_right
        calc 2 ^ (e * Nat.log 2 p) = (2 ^ Nat.log 2 p) ^ e := by ring
          _ ≤ p ^ e := Nat.pow_le_pow_left hle e
  have h2 : e ≤ Nat.log 2 (p ^ e) := by
    calc e = Nat.log 2 (2 ^ e) := by rw [Nat.log_pow (by norm_num : 1 < 2)]
      _ ≤ Nat.log 2 (p ^ e) := Nat.log_mono_right (Nat.pow_le_pow_left hp e)
  nlinarith

end FiniteFieldArith

namespace FiniteFieldArith

/--
[fq_inversion_complexity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma fq_inversion_complexity
  [CommRing R]
  {intMulCost : ℕ → ℕ}
  {K : ℕ}
-- given
  (_hM_ge_id : ∀ n, n ≤ intMulCost n)
  (hM_mono : ∀ a b, a ≤ b → intMulCost a ≤ intMulCost b) :
-- imply
  ∃ C : ℕ, ∀ (p e : ℕ), Nat.Prime p → 0 < e → LogEBoundedByLogP K p e → fqInvCost intMulCost p e ≤ C * intMulCost (C * bitSize (p ^ e)) * (Nat.log 2 (bitSize (p ^ e)) + 1) := by
-- proof
  set C := 2 * K + 5
  refine ⟨C, fun p e hp _he hlog => ?_⟩
  set n := bitSize (p ^ e)
  unfold fqInvCost
  simp only []
  set kb := e * (bitSize p + bitSize e)
  have hkb : kb ≤ C * n := fqInvCost_kb_le p e K hp.two_le hlog
  have hM_kb : intMulCost kb ≤ intMulCost (C * n) := hM_mono _ _ hkb
  have he_le_n : e ≤ n := bitSize_pow_ge_e p e hp.two_le
  have hlog_e : Nat.log 2 e ≤ Nat.log 2 n := Nat.log_mono_right he_le_n
  have hC_ge_2 : 2 ≤ C := by omega
  calc 2 * intMulCost kb * (Nat.log 2 e + 1)
    ≤ 2 * intMulCost (C * n) * (Nat.log 2 n + 1) := by
      apply Nat.mul_le_mul
      · exact Nat.mul_le_mul_left 2 hM_kb
      · omega
    _ ≤ C * intMulCost (C * n) * (Nat.log 2 n + 1) := by
      apply Nat.mul_le_mul_right
      exact Nat.mul_le_mul_right _ hC_ge_2

end FiniteFieldArith

namespace FiniteFieldArith

/--
[kronecker_bitWidth_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma kronecker_bitWidth_le
  [CommRing R]
  {intMulCost : ℕ → ℕ}
  {p e K : ℕ}
-- given
  (hp : 2 ≤ p)
  (hlog : LogEBoundedByLogP K p e) :
-- imply
  kroneckerBitWidth p e ≤ (2 * K + 5) * bitSize (p ^ e) := by
-- proof
  unfold kroneckerBitWidth bitSize LogEBoundedByLogP at *
  have h1 : e * Nat.log 2 p ≤ Nat.log 2 (p ^ e) := by
    have hle : 2 ^ Nat.log 2 p ≤ p := Nat.pow_log_le_self 2 (by omega : p ≠ 0)
    calc e * Nat.log 2 p
      = Nat.log 2 (2 ^ (e * Nat.log 2 p)) := by rw [Nat.log_pow (by norm_num : 1 < 2)]
      _ ≤ Nat.log 2 (p ^ e) := by
        apply Nat.log_mono_right
        calc 2 ^ (e * Nat.log 2 p) = (2 ^ Nat.log 2 p) ^ e := by
          rw [mul_comm, pow_mul]
          _ ≤ p ^ e := Nat.pow_le_pow_left hle e
  have h2 : e ≤ Nat.log 2 (p ^ e) := by
    calc e = Nat.log 2 (2 ^ e) := by rw [Nat.log_pow (by norm_num : 1 < 2)]
      _ ≤ Nat.log 2 (p ^ e) := Nat.log_mono_right (Nat.pow_le_pow_left hp e)
  nlinarith

end FiniteFieldArith

namespace FiniteFieldArith

/--
[fq_mul_complexity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma fq_mul_complexity
  [CommRing R]
  {intMulCost : ℕ → ℕ}
  {p : ℕ}
  {e : ℕ}
  [Fact (Nat.Prime p)]
  {K : ℕ}
  {C_reg : ℕ}
-- given
  (_he : 0 < e)
  (hM_ge_id : ∀ n, n ≤ intMulCost n)
  (hM_mono : ∀ a b, a ≤ b → intMulCost a ≤ intMulCost b)
  (hlog : LogEBoundedByLogP K p e)
  (hM_reg : ∀ n, intMulCost ((2 * K + 5) * n) ≤ C_reg * intMulCost n) :
-- imply
  ∃ C : ℕ, fqMulCost intMulCost p e ≤ C * intMulCost (bitSize (p ^ e)) := by
-- proof
  have hp : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  set n := bitSize (p ^ e)
  set C₀ := 2 * K + 5
  have hkb := kronecker_bitWidth_le p e K hp hlog
  have hkb_C0n : kroneckerBitWidth p e ≤ C₀ * n := hkb
  have hM_kb : intMulCost (kroneckerBitWidth p e) ≤ intMulCost (C₀ * n) :=
    hM_mono _ _ hkb_C0n
  have hM_C0n : intMulCost (C₀ * n) ≤ C_reg * intMulCost n := hM_reg n
  have hM_kb_bound : intMulCost (kroneckerBitWidth p e) ≤ C_reg * intMulCost n :=
    le_trans hM_kb hM_C0n
  have hn_le_Mn : n ≤ intMulCost n := hM_ge_id n
  have hkb_Mn : kroneckerBitWidth p e ≤ C₀ * intMulCost n :=
    le_trans hkb (Nat.mul_le_mul_left C₀ hn_le_Mn)
  refine ⟨2 * C_reg + C₀, ?_⟩
  unfold fqMulCost
  calc 2 * intMulCost (kroneckerBitWidth p e) + kroneckerBitWidth p e
    ≤ 2 * (C_reg * intMulCost n) + C₀ * intMulCost n := by
      linarith [hM_kb_bound, hkb_Mn]
    _ = (2 * C_reg + C₀) * intMulCost n := by ring
end FiniteFieldArith


namespace LongDivision

/--
[longDivAux_rem_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma longDivAux_rem_lt
  [CommRing R]
  {a b : ℕ}
  {k q r : ℕ}
-- given
  (_hb : b ≥ 2)
  (hr : r < b) :
-- imply
  (longDivAux a b k q r).2 < b := by
-- proof
  induction k generalizing q r with
  | zero =>
    unfold longDivAux
    have hle := Bool.toNat_le (a.testBit 0)
    split_ifs with h <;> omega
  | succ k ih =>
    unfold longDivAux
    have hle := Bool.toNat_le (a.testBit (k + 1))
    split_ifs with h
    · exact ih _ _ (by omega)
    · exact ih _ _ (by omega)

end LongDivision

namespace LongDivision

/--
[longDivAux_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma longDivAux_spec
  [CommRing R]
  {a b : ℕ}
  {k q r : ℕ}
-- given
  (_hb : b ≥ 2)
  (hr : r < b) :
-- imply
  (longDivAux a b k q r).1 * b + (longDivAux a b k q r).2 = q * b * 2 ^ (k + 1) + r * 2 ^ (k + 1) + a % 2 ^ (k + 1) := by
-- proof
  induction k generalizing q r with
  | zero =>
    unfold longDivAux
    have hbit := Nat.toNat_testBit a 0
    simp only [pow_zero, Nat.div_one] at hbit
    have hmod : a % 2 ^ 1 = a % 2 := by norm_num
    rw [hmod, ← hbit]
    split_ifs with h
    · zify [h]; ring
    · ring
  | succ k ih =>
    unfold longDivAux
    have hbit := Nat.toNat_testBit a (k + 1)
    have hle := Bool.toNat_le (a.testBit (k + 1))
    have hmod_split : a % 2 ^ (k + 1 + 1) =
      a % 2 ^ (k + 1) + 2 ^ (k + 1) * (a / 2 ^ (k + 1) % 2) := Nat.mod_pow_succ
    split_ifs with h
    · have hr_new : 2 * r + (a.testBit (k + 1)).toNat - b < b := by omega
      rw [ih _ _ hr_new, hmod_split, ← hbit]
      zify [h]; ring
    · have hr_new : 2 * r + (a.testBit (k + 1)).toNat < b := by omega
      rw [ih _ _ hr_new, hmod_split, ← hbit]
      ring

end LongDivision

namespace LongDivision

/--
[longDiv_complexity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma longDiv_complexity
  [CommRing R] :
-- imply
  ∃ C : ℕ, ∀ m n : ℕ, longDivCost m n ≤ C * (m * n) :=
-- proof
  ⟨3, fun m n => by unfold longDivCost; nlinarith⟩
end LongDivision
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
set_option linter.unusedVariables false in


namespace Polynomial

/--
[irreducible_sq_dvd_iff_dvd_derivative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma irreducible_sq_dvd_iff_dvd_derivative
  [CommRing R]
  [Field F]
  [Fintype F]
  [DecidableEq F]
  [Field k]
  [PerfectField k]
  {f g : k[X]}
-- given
  (hirr : Irreducible g) :
-- imply
  g ^ 2 ∣ f ↔ g ∣ f ∧ g ∣ derivative f := by
-- proof
  constructor
  · intro hdvd
    refine ⟨dvd_trans (dvd_pow_self g two_ne_zero) hdvd, ?_⟩
    have h : g ^ 1 ∣ derivative f := pow_sub_one_dvd_derivative_of_pow_dvd hdvd
    rwa [pow_one] at h
  · intro ⟨hf, hf'⟩
    obtain ⟨h, rfl⟩ := hf
    rw [derivative_mul] at hf'
    have hg_dvd_g'h : g ∣ derivative g * h :=
      (dvd_add_left (dvd_mul_right g (derivative h))).mp hf'
    have hsep : g.Separable := PerfectField.separable_of_irreducible hirr
    have hg_dvd_h : g ∣ h := hsep.dvd_of_dvd_mul_left hg_dvd_g'h
    rw [pow_succ, pow_one]
    exact mul_dvd_mul_left g hg_dvd_h

end Polynomial

namespace Polynomial

/--
[irreducible_sq_dvd_iff_dvd_gcd_derivative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma irreducible_sq_dvd_iff_dvd_gcd_derivative
  [CommRing R]
  [Field F]
  [Fintype F]
  [DecidableEq F]
  [Field k]
  [PerfectField k]
  {f g : k[X]}
-- given
  (hirr : Irreducible g) :
-- imply
  g ^ 2 ∣ f ↔ g ∣ EuclideanDomain.gcd f (derivative f) := by
-- proof
  rw [irreducible_sq_dvd_iff_dvd_derivative hirr]
  constructor
  · intro ⟨hf, hf'⟩
    exact EuclideanDomain.dvd_gcd hf hf'
  · intro h
    exact ⟨dvd_trans h (EuclideanDomain.gcd_dvd_left f _),
      dvd_trans h (EuclideanDomain.gcd_dvd_right f _)⟩

end Polynomial

namespace Polynomial

/--
[yunStep_fst](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma yunStep_fst
  [CommRing R]
  [Field F]
  [Fintype F]
  [DecidableEq F]
  [Field k]
  {st : YunState k} :
-- imply
  (yunStep st).1 = EuclideanDomain.gcd st.v (st.w - derivative st.v) :=
-- proof
  rfl

end Polynomial

namespace Polynomial

/--
[yunInit_v](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma yunInit_v
  [CommRing R]
  [Field F]
  [Fintype F]
  [DecidableEq F]
  [Field k]
  {f : k[X]} :
-- imply
  (yunInit f).v = f / EuclideanDomain.gcd f (derivative f) :=
-- proof
  rfl

end Polynomial

namespace Polynomial

/--
[yunInit_w](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma yunInit_w
  [CommRing R]
  [Field F]
  [Fintype F]
  [DecidableEq F]
  [Field k]
  {f : k[X]} :
-- imply
  (yunInit f).w = derivative f / EuclideanDomain.gcd f (derivative f) :=
-- proof
  rfl
/-- Correctness of Yun's algorithm (Algorithm 3.46): for a monic polynomial `f`
over a perfect field with `deg f < char k` (or char = 0), there exist a positive
`m` and pairwise coprime squarefree polynomials `g_0, …, g_{m-1}` such that
`f = ∏_{i} g_i^{i+1}`. -/
section DistinctDegreeFactorization
variable {k : Type*} [Field k] [Fintype k]
open Classical

end Polynomial

namespace Polynomial

/--
[xPowCardPowSubX_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma xPowCardPowSubX_def
  [CommRing R]
  [Field F]
  [Fintype F]
  [DecidableEq F]
  [Field k]
  [Fintype k]
  {j : ℕ} :
-- imply
  xPowCardPowSubX k j = X ^ (Fintype.card k) ^ j - X :=
-- proof
  rfl

end Polynomial

namespace Polynomial

/--
[irreducible_dvd_xPowCardPowSubX_natDegree_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma irreducible_dvd_xPowCardPowSubX_natDegree_dvd
  [CommRing R]
  [Field F]
  [Fintype F]
  [DecidableEq F]
  [Field k]
  [Fintype k]
  {j : ℕ}
  {g : k[X]}
-- given
  (hirr : Irreducible g)
  (hdvd : g ∣ xPowCardPowSubX k j) :
-- imply
  g.natDegree ∣ j := by
-- proof
  unfold xPowCardPowSubX at hdvd
  rw [show (Fintype.card k : ℕ) = Nat.card k from (Nat.card_eq_fintype_card).symm] at hdvd
  exact hirr.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdvd

end Polynomial

namespace Polynomial

/--
[distinctDegreeStep_fst](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma distinctDegreeStep_fst
  [CommRing R]
  [Field F]
  [Fintype F]
  [DecidableEq F]
  [Field k]
  [Fintype k]
  {f : k[X]}
  {j : ℕ} :
-- imply
  (distinctDegreeStep f j).1 = EuclideanDomain.gcd f (xPowCardPowSubX k j) :=
-- proof
  rfl

end Polynomial

namespace Polynomial

/--
[distinctDegreeStep_snd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean)
-/
@[path]
lemma distinctDegreeStep_snd
  [CommRing R]
  [Field F]
  [Fintype F]
  [DecidableEq F]
  [Field k]
  [Fintype k]
  {f : k[X]}
  {j : ℕ} :
-- imply
  (distinctDegreeStep f j).2 = f / EuclideanDomain.gcd f (xPowCardPowSubX k j) :=
-- proof
  rfl

end Polynomial


-- created on 2026-10-23
