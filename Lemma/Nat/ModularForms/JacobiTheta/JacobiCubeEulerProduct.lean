import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.SpecialFunctions.QPochhammer
import Lemma.Complex.QPochhammer
import Lemma.Finset.Enumerative.Partition.RamanujanPartitionCongruence
import sympy.atlas.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruence


namespace MetaMathlibExt.QPochhammer

/--
[coeff_pentagonalSeries_complex_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/JacobiCubeEulerProduct.lean)
-/
@[path]
coefficients of `PowerSeries.pentagonalSeries ℤ`. -/
private lemma coeff_pentagonalSeries_complex_eq (n : ℕ) :
  (PowerSeries.pentagonalSeries ℂ).coeff n
    = (((PowerSeries.pentagonalSeries ℤ).coeff n : ℤ) : ℂ) := by
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    have h1 : (PowerSeries.pentagonalSeries ℂ).coeff (pentagonal k)
      = (-1 : ℂ) ^ k.natAbs := by
      rw [PowerSeries.coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow]
    have h2 : ((((PowerSeries.pentagonalSeries ℤ).coeff (pentagonal k) : ℤ)) : ℂ)
      = (-1 : ℂ) ^ k.natAbs := by
      rw [PowerSeries.coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow,
        Int.cast_pow, Int.cast_neg, Int.cast_one]
    rw [h1, h2]
  · rw [PowerSeries.coeff_pentagonalSeries_eq_zero ℂ hn,
    PowerSeries.coeff_pentagonalSeries_eq_zero ℤ hn, Int.cast_zero]

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[norm_pentCoeff_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/JacobiCubeEulerProduct.lean)
-/
@[path]
in norm. -/
private lemma norm_pentCoeff_le_one (n : ℕ) :
  ‖((((PowerSeries.pentagonalSeries ℤ).coeff n : ℤ)) : ℂ)‖ ≤ 1 := by
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    rw [PowerSeries.coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow,
      Int.cast_pow, Int.cast_neg, Int.cast_one, norm_pow]
    simp
  · rw [PowerSeries.coeff_pentagonalSeries_eq_zero ℤ hn, Int.cast_zero, norm_zero]
    exact zero_le_one

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[summable_norm_pentSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/JacobiCubeEulerProduct.lean)
-/
@[path]
private lemma summable_norm_pentSeries (q : ℂ) (hq : ‖q‖ < 1) :
  Summable fun n : ℕ =>
    ‖(((((PowerSeries.pentagonalSeries ℤ).coeff n : ℤ)) : ℂ)) * q ^ n‖ := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
  · intro n
    calc ‖(((((PowerSeries.pentagonalSeries ℤ).coeff n : ℤ)) : ℂ)) * q ^ n‖
      = ‖(((((PowerSeries.pentagonalSeries ℤ).coeff n : ℤ)) : ℂ))‖ * ‖q‖ ^ n := by
        rw [norm_mul, norm_pow]
      _ ≤ 1 * ‖q‖ ^ n :=
        mul_le_mul_of_nonneg_right (norm_pentCoeff_le_one n)
          (pow_nonneg (norm_nonneg _) n)
      _ = ‖q‖ ^ n := one_mul _
  · exact summable_geometric_of_lt_one (norm_nonneg _) hq

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[hasSum_pentSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/JacobiCubeEulerProduct.lean)
-/
@[path]
`eulerFunction q`. -/
private lemma hasSum_pentSeries (q : ℂ) (hq : ‖q‖ < 1) :
  HasSum (fun n : ℕ =>
    (((((PowerSeries.pentagonalSeries ℤ).coeff n : ℤ)) : ℂ)) * q ^ n)
    (eulerFunction q) := by
  have heuler := hasSum_eulerFunction_pentagonalSeries hq
  refine heuler.congr_fun (fun n => ?_)
  rw [coeff_pentagonalSeries_complex_eq]

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[qPochhammerInf_eq_eulerFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/JacobiCubeEulerProduct.lean)
-/
@[path]
private lemma qPochhammerInf_eq_eulerFunction (q : ℂ) (hq : ‖q‖ < 1) :
  qPochhammerInf q q hq = eulerFunction q := by
  have h := eulerFunction_eq_tprod hq
  unfold qPochhammerInf qPochhammerInfRaw
  rw [h]
  apply tprod_congr
  intro n
  rw [pow_succ']

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[hasSum_mul_of_abs_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/JacobiCubeEulerProduct.lean)
-/
@[path]
if both coefficient series are absolutely summable, their product is the
evaluation of the product series, which is again absolutely summable. -/
private lemma hasSum_mul_of_abs_summable (F G : PowerSeries ℤ) (q : ℂ)
  (hF : Summable fun n : ℕ => ‖(((((F.coeff n : ℤ))) : ℂ)) * q ^ n‖)
  (hG : Summable fun n : ℕ => ‖(((((G.coeff n : ℤ))) : ℂ)) * q ^ n‖) :
  HasSum (fun n : ℕ => ((((((F * G).coeff n : ℤ))) : ℂ)) * q ^ n)
    ((∑' n : ℕ, (((((F.coeff n : ℤ))) : ℂ)) * q ^ n)
      * (∑' n : ℕ, (((((G.coeff n : ℤ))) : ℂ)) * q ^ n))
    ∧ Summable fun n : ℕ => ‖((((((F * G).coeff n : ℤ))) : ℂ)) * q ^ n‖ := by
  have hterm : ∀ n : ℕ, (∑ kl ∈ Finset.antidiagonal n,
    (((((F.coeff kl.1 : ℤ))) : ℂ)) * q ^ kl.1
      * ((((((G.coeff kl.2 : ℤ))) : ℂ)) * q ^ kl.2))
    = ((((((F * G).coeff n : ℤ))) : ℂ)) * q ^ n := by
    intro n
    rw [PowerSeries.coeff_mul, Int.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun kl hkl => ?_)
    obtain ⟨i, k⟩ := kl
    have hmem : i + k = n := Finset.mem_antidiagonal.mp hkl
    have hpair : (((((F.coeff i : ℤ))) : ℂ)) * q ^ i
      * ((((((G.coeff k : ℤ))) : ℂ)) * q ^ k)
      = (((((F.coeff i * G.coeff k : ℤ))) : ℂ)) * q ^ (i + k) := by
      rw [Int.cast_mul, pow_add]
      ring
    rwa [← hmem]
  have hnorm := summable_norm_sum_mul_antidiagonal_of_summable_norm hF hG
  have htsum := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hF hG
  have hHas : HasSum (fun n : ℕ => ((((((F * G).coeff n : ℤ))) : ℂ)) * q ^ n)
    ((∑' n : ℕ, (((((F.coeff n : ℤ))) : ℂ)) * q ^ n)
      * (∑' n : ℕ, (((((G.coeff n : ℤ))) : ℂ)) * q ^ n)) := by
    have h2 := hnorm.of_norm.hasSum.congr_fun (fun n => (hterm n).symm)
    rwa [← htsum] at h2
  exact ⟨hHas, hHas.summable.norm⟩

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[hasSum_pentSeries_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/JacobiCubeEulerProduct.lean)
-/
@[path]
private lemma hasSum_pentSeries_sq (q : ℂ) (hq : ‖q‖ < 1) :
  HasSum (fun n : ℕ =>
    (((((PowerSeries.pentagonalSeries ℤ ^ 2).coeff n : ℤ)) : ℂ)) * q ^ n)
    (eulerFunction q * eulerFunction q)
  ∧ Summable fun n : ℕ =>
    ‖(((((PowerSeries.pentagonalSeries ℤ ^ 2).coeff n : ℤ)) : ℂ)) * q ^ n‖ := by
  have hE := hasSum_pentSeries q hq
  have hN := summable_norm_pentSeries q hq
  have h := hasSum_mul_of_abs_summable _ _ q hN hN
  rw [hE.tsum_eq] at h
  have hsq : PowerSeries.pentagonalSeries ℤ * PowerSeries.pentagonalSeries ℤ
    = PowerSeries.pentagonalSeries ℤ ^ 2 := by
    ring
  rwa [hsq] at h

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[hasSum_pentSeries_cube](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/JacobiCubeEulerProduct.lean)
-/
@[path]
private lemma hasSum_pentSeries_cube (q : ℂ) (hq : ‖q‖ < 1) :
  HasSum (fun n : ℕ =>
    (((((PowerSeries.pentagonalSeries ℤ ^ 3).coeff n : ℤ)) : ℂ)) * q ^ n)
    (eulerFunction q ^ 3)
  ∧ Summable fun n : ℕ =>
    ‖(((((PowerSeries.pentagonalSeries ℤ ^ 3).coeff n : ℤ)) : ℂ)) * q ^ n‖ := by
  have hE := hasSum_pentSeries q hq
  have hN := summable_norm_pentSeries q hq
  obtain ⟨hEE, hEEnorm⟩ := hasSum_pentSeries_sq q hq
  obtain ⟨hEEE, hEEEnorm⟩ := hasSum_mul_of_abs_summable _ _ q hEEnorm hN
  rw [hEE.tsum_eq, hE.tsum_eq] at hEEE
  have hcube : PowerSeries.pentagonalSeries ℤ ^ 2 * PowerSeries.pentagonalSeries ℤ
    = PowerSeries.pentagonalSeries ℤ ^ 3 := by
    ring
  rw [hcube] at hEEE
  have hsum : eulerFunction q * eulerFunction q * eulerFunction q
    = eulerFunction q ^ 3 := by
    ring
  rw [hsum] at hEEE
  have hnorm : Summable fun n : ℕ =>
    ‖(((((PowerSeries.pentagonalSeries ℤ ^ 3).coeff n : ℤ)) : ℂ)) * q ^ n‖ := by
    rwa [← hcube]
  exact ⟨hEEE, hnorm⟩

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[hasSum_jacobiSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/JacobiCubeEulerProduct.lean)
-/
@[path]
private lemma hasSum_jacobiSeries (q : ℂ) (hq : ‖q‖ < 1) :
  HasSum (fun n : ℕ =>
    (((((MetaMathlibExt.jacobiCubeSeries).coeff n : ℤ)) : ℂ)) * q ^ n)
    (eulerFunction q ^ 3) := by
  obtain ⟨hEEE, -⟩ := hasSum_pentSeries_cube q hq
  have hJ : PowerSeries.pentagonalSeries ℤ ^ 3
    = MetaMathlibExt.jacobiCubeSeries :=
    MetaMathlibExt.pentagonalSeries_pow_three
  rwa [hJ] at hEEE

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[strictMono_triangular](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/JacobiCubeEulerProduct.lean)
-/
@[path]
private lemma strictMono_triangular :
  StrictMono (fun t : ℕ => (t + 1).choose 2) := by
  apply strictMono_nat_of_lt_succ
  intro t
  change (t + 1).choose 2 < (t + 1 + 1).choose 2
  have h := Nat.choose_succ_succ' (t + 1) 1
  rw [Nat.choose_one_right] at h
  have e1 : (1 : ℕ) + 1 = 2 := rfl
  rw [e1] at h
  rw [h]
  omega

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[triangular_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/JacobiCubeEulerProduct.lean)
-/
@[path]
private lemma triangular_eq (t : ℕ) : (t + 1).choose 2 = t * (t + 1) / 2 := by
  have h := Nat.choose_two_right (t + 1)
  rw [Nat.add_sub_cancel] at h
  rw [h, mul_comm]

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[jacobi_cast_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/JacobiCubeEulerProduct.lean)
-/
@[path]
private lemma jacobi_cast_eq (t : ℕ) :
  ((((-1 : ℤ) ^ t * (2 * (t : ℤ) + 1) : ℤ)) : ℂ)
    = (-1 : ℂ) ^ t * (((2 * t + 1 : ℕ)) : ℂ) := by
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_add,
    Int.cast_natCast, Int.cast_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one]

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[hasSum_triangular_of_hasSum_jacobi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/JacobiCubeEulerProduct.lean)
-/
@[path]
Wanted sum. -/
private lemma hasSum_triangular_of_hasSum_jacobi (q : ℂ)
  (hJ : HasSum (fun n : ℕ =>
    (((((MetaMathlibExt.jacobiCubeSeries).coeff n : ℤ)) : ℂ)) * q ^ n)
    (eulerFunction q ^ 3)) :
  HasSum (fun t : ℕ =>
    (-1 : ℂ) ^ t * (((2 * t + 1 : ℕ)) : ℂ) * q ^ (t * (t + 1) / 2))
    (eulerFunction q ^ 3) := by
  have hinj : Function.Injective (fun t : ℕ => (t + 1).choose 2) :=
    strictMono_triangular.injective
  have hvan : ∀ b : ℕ, b ∉ Set.range (fun t : ℕ => (t + 1).choose 2) →
    (((((MetaMathlibExt.jacobiCubeSeries).coeff b : ℤ)) : ℂ)) * q ^ b = 0 := by
    intro b hb
    have h0 : MetaMathlibExt.jacobiCubeSeries.coeff b = 0 :=
      MetaMathlibExt.coeff_jacobiCubeSeries_eq_zero (fun t ht => hb ⟨t, ht⟩)
    rw [h0, Int.cast_zero, zero_mul]
  have hre := (hinj.hasSum_iff hvan).mpr hJ
  refine hre.congr_fun (fun t => ?_)
  change (-1 : ℂ) ^ t * ((2 * t + 1 : ℕ) : ℂ) * q ^ (t * (t + 1) / 2)
    = ((MetaMathlibExt.jacobiCubeSeries.coeff ((t + 1).choose 2) : ℤ) : ℂ)
      * q ^ ((t + 1).choose 2)
  rw [MetaMathlibExt.coeff_jacobiCubeSeries_triangle, triangular_eq, jacobi_cast_eq]

end MetaMathlibExt.QPochhammer

namespace MetaMathlibExt.QPochhammer

/--
[jacobi_cube_euler_product_hasSum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/JacobiCubeEulerProduct.lean)
-/
@[path]
lemma jacobi_cube_euler_product_hasSum
  {q : Complex}
-- given
  (hq : ‖q‖ < 1) :
-- imply
  HasSum (fun n : Nat => (-1 : Complex) ^ n * ((2 * n + 1 : Nat) : Complex) *
    q ^ (n * (n + 1) / 2)) ((qPochhammerInf q q hq) ^ 3) := by
-- proof
  have hprod : qPochhammerInf q q hq = eulerFunction q :=
    qPochhammerInf_eq_eulerFunction q hq
  have htri := hasSum_triangular_of_hasSum_jacobi q (hasSum_jacobiSeries q hq)
  rwa [← hprod] at htri

end MetaMathlibExt.QPochhammer


-- created on 2026-10-20
-- updated on 2026-10-23
