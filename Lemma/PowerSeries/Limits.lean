import Mathlib
import sympy.Basic
import sympy.series.formal.Limits
open PowerSeries
open Seq
open scoped PowerSeries BigOperators Polynomial


/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma stabilizes_to_unique_eq
-- given
  {a : ℕ → K}
  {limit1 limit2 : K}
  (ha : StabilizesTo a limit1)
  (hb : StabilizesTo a limit2) :
-- imply
  limit1 = limit2 := by
-- proof
  apply Seq.stabilizesTo_unique ha hb

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma stabilizes_to_const_is
-- given
  (c : K) :
-- imply
  StabilizesTo (fun _ => c) c := by
-- proof
  apply Seq.stabilizesTo_const c

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma stabilizes_to_of_eventually_eq
-- given
  {a b : ℕ → K}
  (heq : ∃ N, ∀ i ≥ N, a i = b i)
  {limit : K}
  (h : StabilizesTo a limit) :
-- imply
  StabilizesTo b limit := by
-- proof
  apply Seq.stabilizesTo_of_eventually_eq h heq

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma stabilizes_to_add_is
  [Add K]
-- given
  {a b : ℕ → K}
  {la lb : K}
  (ha : StabilizesTo a la)
  (hb : StabilizesTo b lb) :
-- imply
  StabilizesTo (fun i => a i + b i) (la + lb) := by
-- proof
  apply Seq.stabilizesTo_add ha hb

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma stabilizes_to_mul_is
  [Mul K]
-- given
  {a b : ℕ → K}
  {la lb : K}
  (ha : StabilizesTo a la)
  (hb : StabilizesTo b lb) :
-- imply
  StabilizesTo (fun i => a i * b i) (la * lb) := by
-- proof
  apply Seq.stabilizesTo_mul ha hb

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma stabilizes_to_neg_is
  [Neg K]
-- given
  {a : ℕ → K}
  {la : K}
  (ha : StabilizesTo a la) :
-- imply
  StabilizesTo (fun i => -a i) (-la) := by
-- proof
  apply Seq.stabilizesTo_neg ha

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma stabilizes_to_pow_of_nilpotent_is
  [MonoidWithZero K]
-- given
  {s : K}
  {k : ℕ}
  (hs : s ^ k = 0) :
-- imply
  StabilizesTo (fun i => s ^ i) 0 := by
-- proof
  apply Seq.stabilizesTo_pow_of_nilpotent hs

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma stabilizes_to_pow_of_idempotent_is
  [Monoid K]
-- given
  {s : K}
  (hs : s * s = s) :
-- imply
  StabilizesTo (fun i => s ^ (i + 1)) s := by
-- proof
  apply Seq.stabilizesTo_pow_of_idempotent hs

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma stabilizes_to_finset_sum_is
  [AddCommMonoid K]
  [DecidableEq ι]
-- given
  {a : ι → ℕ → K}
  {la : ι → K}
  (s : Finset ι)
  (h : ∀ i ∈ s, StabilizesTo (a i) (la i)) :
-- imply
  StabilizesTo (fun n => ∑ i ∈ s, a i n) (∑ i ∈ s, la i) := by
-- proof
  apply Seq.stabilizesTo_finset_sum s h

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_unique_eq
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  {limit1 limit2 : PowerSeries K}
  (ha : CoeffStabilizesTo f limit1)
  (hb : CoeffStabilizesTo f limit2) :
-- imply
  limit1 = limit2 := by
-- proof
  apply PowerSeries.coeffStabilizesTo_unique ha hb

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_const_is
  [CommRing K]
-- given
  (g : PowerSeries K) :
-- imply
  CoeffStabilizesTo (fun _ => g) g := by
-- proof
  apply PowerSeries.coeffStabilizesTo_const g

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_x_pow_is
  [CommRing K] :
-- imply
  CoeffStabilizesTo (fun i => (X : PowerSeries K) ^ i) 0 := by
-- proof
  apply PowerSeries.coeffStabilizesTo_X_pow

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_of_forall_coeff_stabilizes_is
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  {g : ℕ → K}
  (h : ∀ n, Seq.StabilizesTo (fun i => coeff n (f i)) (g n)) :
-- imply
  CoeffStabilizesTo f (mk g) := by
-- proof
  apply PowerSeries.coeffStabilizesTo_of_forall_coeff_stabilizes h

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma xn_equiv_refl_is
  [CommRing K]
-- given
  (n : ℕ)
  (f : PowerSeries K) :
-- imply
  XnEquiv n f f := by
-- proof
  apply PowerSeries.xnEquiv_refl n f

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma xn_equiv_self_eq
  [CommRing K]
-- given
  (n : ℕ)
  (f : PowerSeries K) :
-- imply
  xnEquiv n f f := by
-- proof
  apply PowerSeries.xnEquiv_self n f

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma xn_equiv_symm_is
  [CommRing K]
-- given
  {n : ℕ}
  {f g : PowerSeries K}
  (h : XnEquiv n f g) :
-- imply
  XnEquiv n g f := by
-- proof
  apply PowerSeries.xnEquiv_symm h

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma xn_equiv_trans_is
  [CommRing K]
-- given
  {n : ℕ}
  {f g h : PowerSeries K}
  (hfg : XnEquiv n f g)
  (hgh : XnEquiv n g h) :
-- imply
  XnEquiv n f h := by
-- proof
  apply PowerSeries.xnEquiv_trans hfg hgh

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma xn_equiv_add_is
  [CommRing K]
-- given
  {n : ℕ}
  {f1 f2 g1 g2 : PowerSeries K}
  (hf : XnEquiv n f1 f2)
  (hg : XnEquiv n g1 g2) :
-- imply
  XnEquiv n (f1 + g1) (f2 + g2) := by
-- proof
  apply PowerSeries.xnEquiv_add hf hg

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma xn_equiv_sub_is
  [CommRing K]
-- given
  {n : ℕ}
  {f1 f2 g1 g2 : PowerSeries K}
  (hf : XnEquiv n f1 f2)
  (hg : XnEquiv n g1 g2) :
-- imply
  XnEquiv n (f1 - g1) (f2 - g2) := by
-- proof
  apply PowerSeries.xnEquiv_sub hf hg

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma xn_equiv_smul_is
  [CommRing K]
-- given
  {n : ℕ}
  {f g : PowerSeries K}
  (h : XnEquiv n f g)
  (c : K) :
-- imply
  XnEquiv n (c • f) (c • g) := by
-- proof
  apply PowerSeries.xnEquiv_smul c h

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma xn_equiv_mul_is
  [CommRing K]
-- given
  {n : ℕ}
  {f1 f2 g1 g2 : PowerSeries K}
  (hf : XnEquiv n f1 f2)
  (hg : XnEquiv n g1 g2) :
-- imply
  XnEquiv n (f1 * g1) (f2 * g2) := by
-- proof
  apply PowerSeries.xnEquiv_mul hf hg

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma xn_equiv_pow_is
  [CommRing K]
-- given
  {n : ℕ}
  {f g : PowerSeries K}
  (h : XnEquiv n f g)
  (d : ℕ) :
-- imply
  XnEquiv n (f ^ d) (g ^ d) := by
-- proof
  apply PowerSeries.xnEquiv_pow h d

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma xn_equiv_finset_sum_is
  [CommRing K]
  [DecidableEq ι]
-- given
  {n : ℕ}
  {f g : ι → PowerSeries K}
  (s : Finset ι)
  (h : ∀ i ∈ s, XnEquiv n (f i) (g i)) :
-- imply
  XnEquiv n (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
-- proof
  apply PowerSeries.xnEquiv_finset_sum s h

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma xn_equiv_finset_prod_is
  [CommRing K]
  [DecidableEq ι]
-- given
  {n : ℕ}
  {f g : ι → PowerSeries K}
  (s : Finset ι)
  (h : ∀ i ∈ s, XnEquiv n (f i) (g i)) :
-- imply
  XnEquiv n (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
-- proof
  apply PowerSeries.xnEquiv_finset_prod s h

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_pow_eq_zero_of_constant_coeff_zero_eq
  [CommRing K]
-- given
  (g : PowerSeries K)
  (n d : ℕ)
  (hg : constantCoeff g = 0)
  (hd : d > n) :
-- imply
  coeff n (g ^ d) = 0 := by
-- proof
  apply PowerSeries.coeff_pow_eq_zero_of_constantCoeff_zero g hg n d hd

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_subst_eq_finite_sum_eq
  [CommRing K]
-- given
  (f g : PowerSeries K)
  (hg : constantCoeff g = 0)
  (n : ℕ) :
-- imply
  coeff n (f.subst g) = ∑ d ∈ Finset.range (n + 1), coeff d f • coeff n (g ^ d) := by
-- proof
  apply PowerSeries.coeff_subst_eq_finite_sum f g hg n

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma xn_equiv_subst_is
  [CommRing K]
-- given
  {n : ℕ}
  {f1 f2 g1 g2 : PowerSeries K}
  (hf : XnEquiv n f1 f2)
  (hg : XnEquiv n g1 g2)
  (hg1 : constantCoeff g1 = 0)
  (hg2 : constantCoeff g2 = 0) :
-- imply
  XnEquiv n (f1.subst g1) (f2.subst g2) := by
-- proof
  apply PowerSeries.xnEquiv_subst hf hg hg1 hg2

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_mul_eq_of_coeff_eq
  [CommRing K]
-- given
  {a b c d : PowerSeries K}
  {n : ℕ}
  (hab : ∀ m ≤ n, coeff m a = coeff m b)
  (hcd : ∀ m ≤ n, coeff m c = coeff m d) :
-- imply
  ∀ m ≤ n, coeff m (a * c) = coeff m (b * d) := by
-- proof
  apply PowerSeries.coeff_mul_eq_of_coeff_eq hab hcd

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma xn_equiv_inv_of_unit_is
  [CommRing K]
-- given
  {n : ℕ}
  {f g : PowerSeries K}
  (h : XnEquiv n f g)
  (u : Kˣ) :
-- imply
  XnEquiv n (invOfUnit f u) (invOfUnit g u) := by
-- proof
  apply PowerSeries.xnEquiv_invOfUnit u h

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma xn_equiv_inv_of_unit_prime_is
  [CommRing K]
-- given
  {n : ℕ}
  {f g : PowerSeries K}
  (u v : Kˣ)
  (h : XnEquiv n f g)
  (huv : (u : K) = v) :
-- imply
  XnEquiv n (invOfUnit f u) (invOfUnit g v) := by
-- proof
  apply PowerSeries.xnEquiv_invOfUnit' u v huv h

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma xn_equiv_div_is
  [CommRing K]
-- given
  {n : ℕ}
  {a b c d : PowerSeries K}
  (u v : Kˣ)
  (hab : XnEquiv n a b)
  (hcd : XnEquiv n c d)
  (hu : constantCoeff c = u)
  (hv : constantCoeff d = v) :
-- imply
  XnEquiv n (a * invOfUnit c u) (b * invOfUnit d v) := by
-- proof
  apply PowerSeries.xnEquiv_div hab hcd u hu v hv

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_div_eq_of_coeff_eq
  [CommRing K]
-- given
  {a b c d : PowerSeries K}
  {n : ℕ}
  (u v : Kˣ)
  (hab : ∀ m ≤ n, coeff m a = coeff m b)
  (hcd : ∀ m ≤ n, coeff m c = coeff m d)
  (hu : constantCoeff c = u)
  (hv : constantCoeff d = v) :
-- imply
  ∀ m ≤ n, coeff m (a * invOfUnit c u) = coeff m (b * invOfUnit d v) := by
-- proof
  apply PowerSeries.coeff_div_eq_of_coeff_eq hab hcd u hu v hv

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma exists_xn_equiv_of_coeff_stabilizes_to_is
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  {limit : PowerSeries K}
  (h : CoeffStabilizesTo f limit)
  (n : ℕ) :
-- imply
  ∃ N : ℕ, ∀ i ≥ N, XnEquiv n (f i) limit := by
-- proof
  apply PowerSeries.exists_xnEquiv_of_coeffStabilizesTo h n

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_add_is
  [CommRing K]
-- given
  {f g : ℕ → PowerSeries K}
  {lf lg : PowerSeries K}
  (hf : CoeffStabilizesTo f lf)
  (hg : CoeffStabilizesTo g lg) :
-- imply
  CoeffStabilizesTo (fun i => f i + g i) (lf + lg) := by
-- proof
  apply PowerSeries.coeffStabilizesTo_add hf hg

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_mul_is
  [CommRing K]
-- given
  {f g : ℕ → PowerSeries K}
  {lf lg : PowerSeries K}
  (hf : CoeffStabilizesTo f lf)
  (hg : CoeffStabilizesTo g lg) :
-- imply
  CoeffStabilizesTo (fun i => f i * g i) (lf * lg) := by
-- proof
  apply PowerSeries.coeffStabilizesTo_mul hf hg

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_finset_sum_is
  [CommRing K]
-- given
  {f : ι → ℕ → PowerSeries K}
  {lf : ι → PowerSeries K}
  (s : Finset ι)
  (h : ∀ i ∈ s, CoeffStabilizesTo (f i) (lf i)) :
-- imply
  CoeffStabilizesTo (fun n => ∑ i ∈ s, f i n) (∑ i ∈ s, lf i) := by
-- proof
  apply PowerSeries.coeffStabilizesTo_finset_sum s h

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_finset_prod_is
  [CommRing K]
-- given
  {f : ι → ℕ → PowerSeries K}
  {lf : ι → PowerSeries K}
  (s : Finset ι)
  (h : ∀ i ∈ s, CoeffStabilizesTo (f i) (lf i)) :
-- imply
  CoeffStabilizesTo (fun n => ∏ i ∈ s, f i n) (∏ i ∈ s, lf i) := by
-- proof
  apply PowerSeries.coeffStabilizesTo_finset_prod s h

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_neg_is
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  {lf : PowerSeries K}
  (hf : CoeffStabilizesTo f lf) :
-- imply
  CoeffStabilizesTo (fun i => -f i) (-lf) := by
-- proof
  apply PowerSeries.coeffStabilizesTo_neg hf

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_sub_is
  [CommRing K]
-- given
  {f g : ℕ → PowerSeries K}
  {lf lg : PowerSeries K}
  (hf : CoeffStabilizesTo f lf)
  (hg : CoeffStabilizesTo g lg) :
-- imply
  CoeffStabilizesTo (fun i => f i - g i) (lf - lg) := by
-- proof
  apply PowerSeries.coeffStabilizesTo_sub hf hg

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma is_unit_constant_coeff_of_coeff_stabilizes_to_is
  [CommRing K]
-- given
  {g : ℕ → PowerSeries K}
  (hunit : ∀ i, IsUnit (constantCoeff (g i)))
  {lg : PowerSeries K}
  (hg : CoeffStabilizesTo g lg) :
-- imply
  IsUnit (constantCoeff lg) := by
-- proof
  apply PowerSeries.isUnit_constantCoeff_of_coeffStabilizesTo hg hunit

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma unit_eq_of_coeff_stabilizes_to_is
  [CommRing K]
-- given
  {g : ℕ → PowerSeries K}
  (hunit : ∀ i, IsUnit (constantCoeff (g i)))
  {lg : PowerSeries K}
  (hg : CoeffStabilizesTo g lg) :
-- imply
  ∃ N, ∀ i ≥ N, (hunit i).unit = (isUnit_constantCoeff_of_coeffStabilizesTo hg hunit).unit := by
-- proof
  apply PowerSeries.unit_eq_of_coeffStabilizesTo hg hunit

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_inv_of_unit_is
  [CommRing K]
-- given
  {g : ℕ → PowerSeries K}
  (hunit : ∀ i, IsUnit (constantCoeff (g i)))
  {lg : PowerSeries K}
  (hg : CoeffStabilizesTo g lg) :
-- imply
  CoeffStabilizesTo (fun i => invOfUnit (g i) (hunit i).unit) (invOfUnit lg (isUnit_constantCoeff_of_coeffStabilizesTo hg hunit).unit) := by
-- proof
  apply PowerSeries.coeffStabilizesTo_invOfUnit hg hunit

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_mul_inv_is
  [CommRing K]
-- given
  {f g : ℕ → PowerSeries K}
  (hunit : ∀ i, IsUnit (constantCoeff (g i)))
  {lf lg : PowerSeries K}
  (hf : CoeffStabilizesTo f lf)
  (hg : CoeffStabilizesTo g lg) :
-- imply
  CoeffStabilizesTo (fun i => f i * invOfUnit (g i) (hunit i).unit) (lf * invOfUnit lg (isUnit_constantCoeff_of_coeffStabilizesTo hg hunit).unit) := by
-- proof
  apply PowerSeries.coeffStabilizesTo_mul_inv hf hg hunit

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_subst_is
  [CommRing K]
-- given
  {f g : ℕ → PowerSeries K}
  (hconst : ∀ i, constantCoeff (g i) = 0)
  {lf lg : PowerSeries K}
  (hf : CoeffStabilizesTo f lf)
  (hg : CoeffStabilizesTo g lg) :
-- imply
  CoeffStabilizesTo (fun i => (f i).subst (g i)) (lf.subst lg) := by
-- proof
  apply PowerSeries.coeffStabilizesTo_subst hf hg hconst

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_derivative_is
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  {lf : PowerSeries K}
  (hf : CoeffStabilizesTo f lf) :
-- imply
  CoeffStabilizesTo (fun i => derivative (f i)) (derivative lf) := by
-- proof
  apply PowerSeries.coeffStabilizesTo_derivative hf

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_partial_sum_is
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  (hf : IsSummable f) :
-- imply
  CoeffStabilizesTo (fun i => ∑ j ∈ Finset.range (i + 1), f j) (tsum' f hf) := by
-- proof
  apply PowerSeries.coeffStabilizesTo_partial_sum hf

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_mul_one_plus_higher_le
  [CommRing K]
-- given
  {g f : PowerSeries K}
  {n : ℕ}
  (hf : ∀ k ≤ n, coeff k f = if k = 0 then 1 else 0) :
-- imply
  ∀ k ≤ n, coeff k (g * f) = coeff k g := by
-- proof
  apply PowerSeries.coeff_mul_one_plus_higher hf

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_prod_extend_eq
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  {n m : ℕ}
  (k : ℕ)
  (hf : ∀ k ≤ n, coeff k (f m) = if k = 0 then 1 else 0)
  (hk : k ≤ n) :
-- imply
  coeff k (∏ j ∈ Finset.range (m + 1), f j) = coeff k (∏ j ∈ Finset.range m, f j) := by
-- proof
  apply PowerSeries.coeff_prod_extend hf k hk

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_prod_range_eq_of_ge_eq
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  {n N i k : ℕ}
  (hN : ∀ j ≥ N, ∀ k ≤ n, coeff k (f j) = if k = 0 then 1 else 0)
  (hi : i ≥ N)
  (hk : k ≤ n) :
-- imply
  coeff k (∏ j ∈ Finset.range (i + 1), f j) = coeff k (∏ j ∈ Finset.range (N + 1), f j) := by
-- proof
  apply PowerSeries.coeff_prod_range_eq_of_ge hN hi hk

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_partial_prod_stabilizes_is
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  (hf : IsMultipliable f)
  (n : ℕ) :
-- imply
  ∃ N : ℕ, ∀ i ≥ N, coeff n (∏ j ∈ Finset.range (i + 1), f j) = coeff n (tprod' f hf) := by
-- proof
  apply PowerSeries.coeff_partial_prod_stabilizes hf n

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_partial_prod_is
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  (hf : IsMultipliable f) :
-- imply
  CoeffStabilizesTo (fun i => ∏ j ∈ Finset.range (i + 1), f j) (tprod' f hf) := by
-- proof
  apply PowerSeries.coeffStabilizesTo_partial_prod hf

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_trunc_is
  [CommRing K]
-- given
  (a : PowerSeries K) :
-- imply
  CoeffStabilizesTo (fun i => (trunc (i + 1) a : PowerSeries K)) a := by
-- proof
  apply PowerSeries.coeffStabilizesTo_trunc a

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma is_summable_of_coeff_stabilizes_to_partial_sum_is
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  {limit : PowerSeries K}
  (h : CoeffStabilizesTo (fun i => ∑ j ∈ Finset.range (i + 1), f j) limit) :
-- imply
  IsSummable f := by
-- proof
  apply PowerSeries.isSummable_of_coeffStabilizesTo_partial_sum h

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma tsum_prime_eq_of_coeff_stabilizes_to_partial_sum_eq
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  {limit : PowerSeries K}
  (h : CoeffStabilizesTo (fun i => ∑ j ∈ Finset.range (i + 1), f j) limit) :
-- imply
  tsum' f (isSummable_of_coeffStabilizesTo_partial_sum h) = limit := by
-- proof
  apply PowerSeries.tsum'_eq_of_coeffStabilizesTo_partial_sum h

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma constant_coeff_prod_eq_one_eq
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  {s : Finset ℕ}
  (hf : ∀ i ∈ s, constantCoeff (f i) = 1) :
-- imply
  constantCoeff (∏ j ∈ s, f j) = 1 := by
-- proof
  apply PowerSeries.constantCoeff_prod_eq_one hf

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma is_multipliable_of_coeff_stabilizes_to_partial_prod_is
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  (hconst : ∀ i, constantCoeff (f i) = 1)
  {limit : PowerSeries K}
  (h : CoeffStabilizesTo (fun i => ∏ j ∈ Finset.range (i + 1), f j) limit) :
-- imply
  IsMultipliable f := by
-- proof
  apply PowerSeries.isMultipliable_of_coeffStabilizesTo_partial_prod h hconst

/--
[Limits](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Limits.lean)
-/
@[path]
private lemma tprod_prime_eq_of_coeff_stabilizes_to_partial_prod_eq
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  (hconst : ∀ i, constantCoeff (f i) = 1)
  {limit : PowerSeries K}
  (h : CoeffStabilizesTo (fun i => ∏ j ∈ Finset.range (i + 1), f j) limit) :
-- imply
  tprod' f (isMultipliable_of_coeffStabilizesTo_partial_prod h hconst) = limit := by
-- proof
  apply PowerSeries.tprod'_eq_of_coeffStabilizesTo_partial_prod h hconst


-- created on 2026-10-12
