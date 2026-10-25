/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalFamily.Part4
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSechFourier.Part2
open Filter MeasureTheory Set Topology
open scoped FourierTransform


namespace StatMech.FrontierD

noncomputable section

theorem summable_sixVertexSechPhaseTerm
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    Summable (sixVertexSechPhaseTerm lam alpha) := by
  apply Summable.of_norm
  exact (summable_fourier_sixVertexSechProfile_int hlam).norm.congr fun n => by
    unfold sixVertexSechPhaseTerm
    rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one,
      fourier_sixVertexSechProfile hlam]

theorem sixVertexSechPhaseTerm_pair
    (lam alpha : Real) (n : Nat) :
    sixVertexSechPhaseTerm lam alpha (Int.ofNat (n + 1)) +
        sixVertexSechPhaseTerm lam alpha (-Int.ofNat (n + 1)) =
      (sixVertexFourierRootDensityTerm lam n alpha : Complex) := by
  let m : Real := n + 1
  have hm : (m : Complex) = ((Int.ofNat (n + 1) : Int) : Complex) := by
    dsimp [m]
    norm_num
  have hphasePos :
      2 * (Real.pi : Complex) * Complex.I *
          ((Int.ofNat (n + 1) : Int) : Complex) *
            (alpha / (2 * Real.pi) : Real) =
        ((m * alpha : Real) : Complex) * Complex.I := by
    rw [← hm]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hphaseNeg :
      2 * (Real.pi : Complex) * Complex.I *
          ((-Int.ofNat (n + 1) : Int) : Complex) *
            (alpha / (2 * Real.pi) : Real) =
        -((m * alpha : Real) : Complex) * Complex.I := by
    push_cast
    rw [← hm]
    push_cast
    field_simp [Real.pi_ne_zero]
  unfold sixVertexSechPhaseTerm
  rw [fourier_coe_apply, fourier_coe_apply]
  simp only [Complex.ofReal_one, div_one]
  rw [hphasePos, hphaseNeg]
  have hcoshNeg :
      Real.cosh (((-Int.ofNat (n + 1) : Int) : Real) * lam) =
        Real.cosh (m * lam) := by
    rw [show (((-Int.ofNat (n + 1) : Int) : Real) * lam) =
      -(m * lam) by
        dsimp [m]
        push_cast
        ring,
      Real.cosh_neg]
  rw [hcoshNeg]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  unfold sixVertexFourierRootDensityTerm
  dsimp [m]
  push_cast
  simp only [Complex.cos_neg, Complex.sin_neg]
  ring

theorem ofReal_sixVertexFourierRootDensity_eq_tsum_phase
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    (sixVertexFourierRootDensity lam alpha : Complex) =
      ∑' n : Int, sixVertexSechPhaseTerm lam alpha n := by
  let f : Int → Complex := sixVertexSechPhaseTerm lam alpha
  have hf : Summable f := summable_sixVertexSechPhaseTerm hlam alpha
  have hinjPos : Function.Injective (fun n : PNat => (n : Int)) := by
    intro m n hmn
    exact Subtype.ext (Int.ofNat_inj.mp hmn)
  have hinjNeg : Function.Injective (fun n : PNat => -(n : Int)) := by
    intro m n hmn
    apply hinjPos
    exact neg_injective hmn
  have hpos : Summable (fun n : PNat => f (n : Int)) := by
    simpa only [Function.comp_def] using hf.comp_injective hinjPos
  have hneg : Summable (fun n : PNat => f (-(n : Int))) := by
    simpa only [Function.comp_def] using hf.comp_injective hinjNeg
  have hzero : f 0 = (1 / 2 : Complex) := by
    unfold f sixVertexSechPhaseTerm
    rw [fourier_coe_apply]
    norm_num
  let pair : PNat → Complex := fun p =>
    f (p : Int) + f (-(p : Int))
  have hpair :
      (∑' p : PNat, pair p) =
        ∑' n : Nat,
          (sixVertexFourierRootDensityTerm lam n alpha : Complex) := by
    rw [← Equiv.pnatEquivNat.tsum_eq (fun n : Nat =>
      (sixVertexFourierRootDensityTerm lam n alpha : Complex))]
    apply tsum_congr
    intro p
    dsimp [pair, f]
    simpa [Equiv.pnatEquivNat] using
      sixVertexSechPhaseTerm_pair lam alpha (Equiv.pnatEquivNat p)
  calc
    (sixVertexFourierRootDensity lam alpha : Complex) =
        (1 / 2 : Complex) +
          ∑' n : Nat,
            (sixVertexFourierRootDensityTerm lam n alpha : Complex) := by
      rw [sixVertexFourierRootDensity, Complex.ofReal_add,
        Complex.ofReal_tsum]
      congr 1
      norm_num
    _ = f 0 + ∑' p : PNat, pair p := by
      rw [hzero, hpair]
    _ = f 0 + (∑' n : PNat, f (n : Int)) +
        ∑' n : PNat, f (-(n : Int)) := by
      have hpairSum : (∑' p : PNat, pair p) =
          (∑' p : PNat, f (p : Int)) +
            ∑' p : PNat, f (-(p : Int)) := by
        dsimp [pair]
        exact hpos.tsum_add hneg
      rw [hpairSum]
      abel
    _ = ∑' n : Int, f n := by
      rw [tsum_int_eq_zero_add_tsum_pnat hf]
    _ = ∑' n : Int, sixVertexSechPhaseTerm lam alpha n := rfl

theorem summable_sixVertexSechProfile_shift
    {lam : Real} (hlam : 0 < lam) (x : Real) :
    Summable (fun n : Int => sixVertexSechProfile lam (x + n)) := by
  let f : C(Real, Complex) :=
    ⟨sixVertexSechProfile lam, continuous_sixVertexSechProfile hlam⟩
  let K : TopologicalSpace.Compacts Real :=
    ⟨{x}, isCompact_singleton⟩
  have hrestrict : Summable (fun n : Int =>
      ‖(f.comp (ContinuousMap.addRight (n : Real))).restrict K‖) := by
    apply summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    exact ((isBigO_norm_restrict_cocompact f (by norm_num)
      (isBigO_sixVertexSechProfile_cocompact hlam) K).comp_tendsto
        Int.tendsto_coe_cofinite)
  apply hrestrict.of_norm_bounded
  intro n
  exact ContinuousMap.norm_coe_le_norm
    ((f.comp (ContinuousMap.addRight (n : Real))).restrict K) ⟨x, by simp [K]⟩

theorem sixVertexFourierRootDensity_eq_tsum_sechProfile
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    sixVertexFourierRootDensity lam alpha =
      ∑' n : Int,
        Real.pi / (2 * lam) /
          Real.cosh (Real.pi ^ 2 *
            (alpha / (2 * Real.pi) + n) / lam) := by
  let x : Real := alpha / (2 * Real.pi)
  let g : Int → Real := fun n =>
    Real.pi / (2 * lam) /
      Real.cosh (Real.pi ^ 2 * (x + n) / lam)
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  calc
    (sixVertexFourierRootDensity lam alpha : Complex) =
        ∑' n : Int, sixVertexSechPhaseTerm lam alpha n :=
      ofReal_sixVertexFourierRootDensity_eq_tsum_phase hlam alpha
    _ = ∑' n : Int, sixVertexSechProfile lam (x + n) := by
      rw [sixVertexSechProfile_poisson hlam x]
      apply tsum_congr
      intro n
      rfl
    _ = ∑' n : Int, (g n : Complex) := by
      apply tsum_congr
      intro n
      rfl

theorem sixVertexFourierRootDensity_pos
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    0 < sixVertexFourierRootDensity lam alpha := by
  let x : Real := alpha / (2 * Real.pi)
  let g : Int → Real := fun n =>
    Real.pi / (2 * lam) /
      Real.cosh (Real.pi ^ 2 * (x + n) / lam)
  have hcomplex := summable_sixVertexSechProfile_shift hlam x
  have hnorm : Summable (fun n : Int => ‖g n‖) := by
    have h := hcomplex.norm
    simpa only [sixVertexSechProfile, Complex.norm_real] using h
  have hg : Summable g := Summable.of_norm hnorm
  have hnonneg (n : Int) : 0 ≤ g n := by
    dsimp [g]
    positivity
  have hzero : 0 < g 0 := by
    dsimp [g, x]
    positivity
  rw [sixVertexFourierRootDensity_eq_tsum_sechProfile hlam alpha]
  change 0 < ∑' n : Int, g n
  exact hg.tsum_pos hnonneg 0 hzero

theorem sixVertexFourierPhysicalDensity_pos
    {c : Real} (hc : 2 < c) (x : Real) :
    0 < sixVertexFourierPhysicalDensity c hc x := by
  unfold sixVertexFourierPhysicalDensity
  exact div_pos
    (sixVertexFourierRootDensity_pos
      (sixVertexAntiferroelectricLambda_pos hc) _)
    (mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (sixVertexRootDensityWeight_pos hc x))

theorem sixVertexFourierPhysicalDensityFamily_pos
    {a b : Real} (ha : 2 < a) (z : Set.Icc a b × Real) :
    0 < sixVertexFourierPhysicalDensityFamily (b := b) ha z := by
  rw [sixVertexFourierPhysicalDensityFamily_apply]
  exact sixVertexFourierPhysicalDensity_pos (ha.trans_le z.1.2.1) z.2

theorem exists_uniformLower_sixVertexFourierPhysicalDensityFamily
    {a b : Real} (ha : 2 < a) (hab : a ≤ b) :
    ∃ rhoLower : Real, 0 < rhoLower ∧
      ∀ (t : Set.Icc a b) (x : Real),
        rhoLower ≤ sixVertexContinuumDensityAt
          (sixVertexFourierPhysicalDensityFamily ha) t x := by
  let X := Set.Icc a b × Set.Icc (-Real.pi) Real.pi
  let upperWeight : Set.Icc a b → Real := fun t =>
    (sixVertexAnisotropyMagnitude t.1 + 1) /
      sixVertexRootDensityScale t.1
  let proxy : X → Real := fun z =>
    sixVertexFourierRootDensity
        (sixVertexAntiferroelectricLambda z.1.1) z.2.1 /
      (2 * Real.pi * upperWeight z.1)
  let incl : X → Set.Icc a b × Real := fun z => (z.1, z.2.1)
  have hincl : Continuous incl := by
    exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hnum : Continuous (fun z : X =>
      sixVertexFourierRootDensity
        (sixVertexAntiferroelectricLambda z.1.1) z.2.1) := by
    have h := (continuous_sixVertexFourierRootDensity_family (b := b) ha).comp hincl
    simpa only [incl] using h
  have hupper : Continuous upperWeight := by
    have hmag : Continuous (fun t : Set.Icc a b =>
        sixVertexAnisotropyMagnitude t.1) := by
      unfold sixVertexAnisotropyMagnitude sixVertexDelta
      fun_prop
    have hscale : Continuous (fun t : Set.Icc a b =>
        sixVertexRootDensityScale t.1) := by
      unfold sixVertexRootDensityScale
      exact Real.continuous_sqrt.comp ((hmag.pow 2).sub continuous_const)
    dsimp only [upperWeight]
    apply (hmag.add continuous_const).div hscale
    · intro t
      exact (sixVertexRootDensityScale_pos
        (ha.trans_le t.2.1)).ne'
  have hproxy : Continuous proxy := by
    dsimp [proxy]
    apply hnum.div
    · exact continuous_const.mul (hupper.comp continuous_fst)
    · intro z
      have hc : 2 < z.1.1 := ha.trans_le z.1.2.1
      exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (div_ne_zero
          (by linarith [one_lt_sixVertexAnisotropyMagnitude hc])
          (sixVertexRootDensityScale_pos hc).ne')
  let zdefault : X :=
    (⟨a, ⟨le_rfl, hab⟩⟩,
      ⟨0, ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩⟩)
  obtain ⟨z, _hzuniv, hzmin⟩ := isCompact_univ.exists_isMinOn
    ⟨zdefault, Set.mem_univ _⟩ hproxy.continuousOn
  have hzpos : 0 < proxy z := by
    dsimp [proxy, upperWeight]
    have hc : 2 < z.1.1 := ha.trans_le z.1.2.1
    apply div_pos
    · exact sixVertexFourierRootDensity_pos
        (sixVertexAntiferroelectricLambda_pos hc) z.2.1
    · exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
        (div_pos
          (by linarith [one_lt_sixVertexAnisotropyMagnitude hc])
          (sixVertexRootDensityScale_pos hc))
  refine ⟨proxy z, hzpos, ?_⟩
  intro t x
  have hc : 2 < t.1 := ha.trans_le t.2.1
  let lam := sixVertexAntiferroelectricLambda t.1
  let alpha := sixVertexMomentumRapidity lam
    (sixVertexAntiferroelectricLambda_pos hc) x
  have halpha : alpha ∈ Set.Icc (-Real.pi) Real.pi := by
    dsimp [alpha]
    unfold sixVertexMomentumRapidity
    exact ((sixVertexRapidityMomentumOrderIso lam
      (sixVertexAntiferroelectricLambda_pos hc)).symm
        (Set.projIcc (-Real.pi) Real.pi
          (by linarith [Real.pi_pos]) x)).property
  let y : X := (t, ⟨alpha, halpha⟩)
  have hmin : proxy z ≤ proxy y := hzmin (Set.mem_univ y)
  refine hmin.trans ?_
  have hnumPos : 0 < sixVertexFourierRootDensity lam alpha :=
    sixVertexFourierRootDensity_pos
      (sixVertexAntiferroelectricLambda_pos hc) alpha
  have hweightPos : 0 < sixVertexRootDensityWeight t.1 x :=
    sixVertexRootDensityWeight_pos hc x
  have hweightLe := sixVertexRootDensityWeight_le hc x
  simp only [sixVertexContinuumDensityAt, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, sixVertexFourierPhysicalDensityFamily_apply]
  unfold sixVertexFourierPhysicalDensity
  change proxy y ≤
    sixVertexFourierRootDensity lam alpha /
      (2 * Real.pi * sixVertexRootDensityWeight t.1 x)
  dsimp [proxy, upperWeight, y]
  apply div_le_div_of_nonneg_left hnumPos.le
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) hweightPos)
  exact mul_le_mul_of_nonneg_left hweightLe
    (mul_nonneg (by norm_num) Real.pi_pos.le)

theorem fourier_sech
    {lam : Real} (hlam : 0 < lam) (n : Real) :
    FourierTransform.fourier (fun x : Real =>
      ((1 / Real.cosh (Real.pi ^ 2 * x / lam) : Real) : Complex)) n =
      (lam / Real.pi : Real) / Real.cosh (n * lam) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul, Complex.ofReal_div, Complex.ofReal_one]
  rw [show (fun v : Real =>
      Complex.exp ((-2 * Real.pi * v * n : Real) * Complex.I) *
        (1 / (Real.cosh (Real.pi ^ 2 * v / lam) : Complex))) =
      fun v =>
        Complex.exp ((-2 * Real.pi * (v * n) : Real) * Complex.I) /
          Real.cosh (Real.pi ^ 2 * v / lam) by
    funext v
    push_cast
    ring]
  simpa only [Complex.ofReal_div] using integral_fourier_sech hlam n

end
end StatMech.FrontierD
