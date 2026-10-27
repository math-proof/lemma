/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Separation.CompletelyRegular
import Def.Analysis.Fourier.Bochner


section

open MeasureTheory Complex

open scoped BigOperators

namespace Fourier.BochnerWanted

/-- Kernel nonnegativity (N5): one instance of positive-definiteness. -/
lemma bochnerKernel_im_eq_zero_and_re_nonneg
    {f : ℝ → ℂ}
    (hpd : ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
      let S := ∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * f (x i - x j)
      S.im = 0 ∧ 0 ≤ S.re)
    (h : ℝ) (N : ℕ) (ξ : ℝ) :
    (bochnerKernel f h N ξ).im = 0 ∧ 0 ≤ (bochnerKernel f h N ξ).re := by
  let x : Fin N → ℝ := fun j => (j : ℝ) * h
  let c : Fin N → ℂ := fun l => cexp ((((l : ℝ) * h * ξ : ℝ) : ℂ) * I)
  have hS := hpd N x c
  dsimp only at hS
  obtain ⟨him, hre⟩ := hS
  have hstar : ∀ a : ℝ, star (cexp ((((a * h * ξ : ℝ)) : ℂ) * I) : ℂ)
      = cexp ((((-(a * h * ξ)) : ℝ) : ℂ) * I) := by
    intro a
    change (starRingEnd ℂ) _ = _
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal, Complex.conj_I]
  have hexp : ∀ j l : Fin N,
      ((((-(((j : ℝ)) * h * ξ)) : ℝ) : ℂ) * I + ((((l : ℝ) * h * ξ : ℝ)) : ℂ) * I)
        = (((-((((j : ℝ) - (l : ℝ))) * h * ξ) : ℝ) : ℂ) * I) := by
    intro j l
    push_cast
    ring
  have heq : (∑ i : Fin N, ∑ j : Fin N, star (c i) * c j * f (x i - x j))
      = bochnerKernel f h N ξ := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    have e1 : star (c j) * c l * f (x j - x l)
        = f (((j : ℝ) - (l : ℝ)) * h) * (cexp ((((-(((j : ℝ)) * h * ξ)) : ℝ) : ℂ) * I) *
          cexp (((((l : ℝ) * h * ξ : ℝ)) : ℂ) * I)) := by
      simp only [x, c]
      rw [hstar ((j : ℝ))]
      have hx : (j : ℝ) * h - (l : ℝ) * h = ((j : ℝ) - (l : ℝ)) * h := by ring
      rw [hx]
      ring
    rw [e1, ← Complex.exp_add, hexp j l]
  rw [heq] at him hre
  exact ⟨him, hre⟩

/-- Characteristic function of a finitely supported measure (N7). -/
lemma charFun_finsetSum_smul_dirac
    {ι : Type*} (s : Finset ι) (p : ι → ℝ) (w : ι → ℝ) (hw : ∀ r ∈ s, 0 ≤ w r) (t : ℝ) :
    charFun (∑ r ∈ s, ENNReal.ofReal (w r) • Measure.dirac (p r)) t
      = ∑ r ∈ s, (w r : ℂ) * cexp (↑t * ↑(p r) * I) := by
  have hbase : ∀ (r : ι), Integrable (fun y : ℝ => cexp (↑t * ↑y * I)) (Measure.dirac (p r)) := by
    intro r
    apply Integrable.of_bound (C := 1)
    · exact ((Complex.continuous_exp.comp
        ((continuous_const.mul continuous_ofReal).mul continuous_const)).aestronglyMeasurable)
    · filter_upwards with y
      rw [show (↑t * ↑y * I : ℂ) = ↑(t * y) * I by push_cast; ring]
      rw [Complex.norm_exp_ofReal_mul_I]
  have hInt : ∀ r ∈ s, Integrable (fun y : ℝ => cexp (↑t * ↑y * I))
      (ENNReal.ofReal (w r) • Measure.dirac (p r)) := by
    intro r hr
    exact (hbase r).smul_measure ENNReal.ofReal_ne_top
  rw [charFun_apply_real, MeasureTheory.integral_finsetSum_measure hInt]
  apply Finset.sum_congr rfl
  intro r hr
  rw [MeasureTheory.integral_smul_measure]
  rw [MeasureTheory.integral_dirac]
  simp [ENNReal.toReal_ofReal (hw r hr), Complex.real_smul]

/-- Discrete orthogonality of characters on `ℤ / 2N` (N3). -/
lemma sum_range_exp_pi_int_mul_div (N : ℕ) (hN : 1 ≤ N) (q : ℤ)
    (hq : |q| < 2 * (N : ℤ)) :
    (∑ r ∈ Finset.range (2 * N),
      cexp (((Real.pi * (q : ℝ) * ((r : ℝ) - (N : ℝ)) / (N : ℝ) : ℝ) : ℂ)
        * Complex.I))
      = if q = 0 then ((2 * N : ℕ) : ℂ) else 0 := by
  have hNe : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNeC : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  by_cases hq0 : q = 0
  · subst hq0
    rw [ite_eq_left rfl]
    have h1 : ∀ r ∈ Finset.range (2 * N),
        cexp (((Real.pi * ((0 : ℤ) : ℝ) * ((r : ℝ) - (N : ℝ)) / (N : ℝ) : ℝ) : ℂ)
          * Complex.I) = 1 := by
      intro r _
      have harg0 : (((Real.pi * ((0 : ℤ) : ℝ) * ((r : ℝ) - (N : ℝ)) / (N : ℝ) : ℝ)
        : ℂ) * Complex.I) = 0 := by simp
      rw [harg0, Complex.exp_zero]
    rw [show (∑ r ∈ Finset.range (2 * N),
        cexp (((Real.pi * ((0 : ℤ) : ℝ) * ((r : ℝ) - (N : ℝ)) / (N : ℝ) : ℝ) : ℂ)
          * Complex.I)) = ∑ _r ∈ Finset.range (2 * N), 1 from
      Finset.sum_congr rfl (fun r hr => h1 r hr)]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · rw [ite_eq_right hq0]
    have hexpR : ∀ r : ℝ, Real.pi * (q : ℝ) * (r - (N : ℝ)) / (N : ℝ)
        = r * ((q : ℝ) * Real.pi / (N : ℝ)) - Real.pi * (q : ℝ) := by
      intro r
      field_simp
    have hterm : ∀ r ∈ Finset.range (2 * N),
        cexp (((Real.pi * (q : ℝ) * ((r : ℝ) - (N : ℝ)) / (N : ℝ) : ℝ) : ℂ)
          * Complex.I)
          = cexp (((-(Real.pi * (q : ℝ)) : ℝ) : ℂ) * Complex.I)
            * (cexp ((((q : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)) ^ r := by
      intro r _
      have harg : (((Real.pi * (q : ℝ) * ((r : ℝ) - (N : ℝ)) / (N : ℝ) : ℝ) : ℂ)
          * Complex.I)
          = (((-(Real.pi * (q : ℝ)) : ℝ) : ℂ) * Complex.I)
            + (r : ℂ) * ((((q : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ)
              * Complex.I) := by
        rw [hexpR]
        push_cast
        ring
      rw [harg, Complex.exp_add, Complex.exp_nat_mul]
    have hsum : (∑ r ∈ Finset.range (2 * N),
        cexp (((Real.pi * (q : ℝ) * ((r : ℝ) - (N : ℝ)) / (N : ℝ) : ℝ) : ℂ)
          * Complex.I))
        = cexp (((-(Real.pi * (q : ℝ)) : ℝ) : ℂ) * Complex.I)
          * ∑ r ∈ Finset.range (2 * N),
            (cexp ((((q : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)) ^ r := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun r hr => hterm r hr)
    have hBM : (cexp ((((q : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I))
        ^ (2 * N) = 1 := by
      rw [← Complex.exp_nat_mul]
      have hargM : ((2 * N : ℕ) : ℂ)
          * ((((q : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
          = (q : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        field_simp
      rw [hargM]
      exact Complex.exp_int_mul_two_pi_mul_I q
    have hω : IsPrimitiveRoot
        (cexp (2 * Real.pi * Complex.I
          * (((1 : ℤ) : ℂ) / ((2 * N : ℕ) : ℂ)))) (2 * N) :=
      Complex.isPrimitiveRoot_exp_of_isCoprime 1 (2 * N)
        (by omega) isCoprime_one_left
    have hBpow : (cexp (2 * Real.pi * Complex.I
        * (((1 : ℤ) : ℂ) / ((2 * N : ℕ) : ℂ)))) ^ (q : ℤ)
        = cexp ((((q : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_int_mul]
      congr 1
      push_cast
      field_simp
    have hBne : cexp ((((q : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
        ≠ 1 := by
      intro hcon
      have hdvd : ((2 * N : ℕ) : ℤ) ∣ q :=
        (IsPrimitiveRoot.zpow_eq_one_iff_dvd hω q).mp (by rw [hBpow]; exact hcon)
      have hq0' : q = 0 := Int.eq_zero_of_abs_lt_dvd hdvd (by push_cast; exact hq)
      exact hq0 hq0'
    rw [hsum, geom_sum_eq hBne (2 * N), hBM, sub_self, zero_div, mul_zero]

/-- Toeplitz / Fejér pair counting, `m ≥ 0` case (N4). -/
lemma card_fin_pairs_sub_eq_of_nonneg (N : ℕ) (m : ℤ) (hm0 : 0 ≤ m)
    (hm : |m| ≤ (N : ℤ)) :
    (Finset.univ.filter
      (fun p : Fin N × Fin N => (p.1 : ℤ) - (p.2 : ℤ) = m)).card
      = N - m.natAbs := by
  have hle : m.natAbs ≤ N := by
    have h : ((m.natAbs : ℕ) : ℤ) ≤ (N : ℤ) := by
      rw [Int.natCast_natAbs]
      exact hm
    exact_mod_cast h
  have hmnat : ((m.natAbs : ℕ) : ℤ) = m := by
    rw [Int.natCast_natAbs, abs_of_nonneg hm0]
  have hcard : (Finset.univ : Finset (Fin (N - m.natAbs))).card
      = (Finset.univ.filter
        (fun p : Fin N × Fin N => (p.1 : ℤ) - (p.2 : ℤ) = m)).card := by
    refine Finset.card_bij'
      (fun k _ => ((⟨k.val + m.natAbs, by
            have hk := k.2
            omega⟩ : Fin N),
        (⟨k.val, by
          have hk := k.2
          omega⟩ : Fin N)))
      (fun p hp => (⟨p.2.val, by
          have hp2 : (p.1 : ℤ) - (p.2 : ℤ) = m :=
            (Finset.mem_filter.mp hp).2
          have h1 := p.1.2
          have h2 := p.2.2
          omega⟩ : Fin (N - m.natAbs))) ?hi ?hj ?li ?ri
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_add, hmnat]
      omega
    · intro p hp
      exact Finset.mem_univ _
    · intro k hk
      exact Fin.ext rfl
    · intro p hp
      have hp2 : (p.1 : ℤ) - (p.2 : ℤ) = m := (Finset.mem_filter.mp hp).2
      have hfst : p.1.val = p.2.val + m.natAbs := by omega
      apply Prod.ext_iff.mpr
      constructor
      · apply Fin.ext
        change p.2.val + m.natAbs = p.1.val
        exact hfst.symm
      · exact Fin.ext rfl
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  exact hcard.symm

/-- Toeplitz / Fejér pair counting (N4). -/
lemma card_fin_pairs_sub_eq (N : ℕ) (m : ℤ) (hm : |m| ≤ (N : ℤ)) :
    (Finset.univ.filter
      (fun p : Fin N × Fin N => (p.1 : ℤ) - (p.2 : ℤ) = m)).card
      = N - m.natAbs := by
  rcases le_total 0 m with hm0 | hmneg
  · exact card_fin_pairs_sub_eq_of_nonneg N m hm0 hm
  · have hm0' : 0 ≤ -m := neg_nonneg.mpr hmneg
    have hm' : |-m| ≤ (N : ℤ) := by
      rw [abs_neg]
      exact hm
    have hmain := card_fin_pairs_sub_eq_of_nonneg N (-m) hm0' hm'
    have hneg : (-m).natAbs = m.natAbs := by omega
    rw [hneg] at hmain
    have hmap : (Finset.univ.filter
        (fun p : Fin N × Fin N => (p.1 : ℤ) - (p.2 : ℤ) = m)).map
        (Equiv.prodComm (Fin N) (Fin N)).toEmbedding
        = Finset.univ.filter
          (fun p : Fin N × Fin N => (p.1 : ℤ) - (p.2 : ℤ) = -m) := by
      ext x
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy2 : (y.1 : ℤ) - (y.2 : ℤ) = m := hy
        change (y.2 : ℤ) - (y.1 : ℤ) = -m
        omega
      · intro hx
        have hx2 : (x.1 : ℤ) - (x.2 : ℤ) = -m := hx
        refine ⟨(x.2, x.1), ?_, rfl⟩
        change (x.2 : ℤ) - (x.1 : ℤ) = m
        omega
    have hcardmap := Finset.card_map (s := Finset.univ.filter
        (fun p : Fin N × Fin N => (p.1 : ℤ) - (p.2 : ℤ) = m))
      (Equiv.prodComm (Fin N) (Fin N)).toEmbedding
    rw [hmap, hmain] at hcardmap
    exact hcardmap.symm

/-- N4 in sum form, as used by the kernel lattice sum (N6). -/
lemma sum_fin_pairs_sub_eq (N : ℕ) (m : ℤ) (hm : |m| ≤ (N : ℤ)) :
    (∑ j : Fin N, ∑ l : Fin N,
      (if (j : ℤ) - (l : ℤ) = m then (1 : ℂ) else 0))
      = (N : ℂ) - (((|m| : ℤ)) : ℂ) := by
  have hcard := card_fin_pairs_sub_eq N m hm
  rw [← Fintype.sum_prod_type', Finset.sum_boole, hcard]
  have hle : m.natAbs ≤ N := by
    have h : ((m.natAbs : ℕ) : ℤ) ≤ (N : ℤ) := by
      rw [Int.natCast_natAbs]
      exact hm
    exact_mod_cast h
  rw [Nat.cast_sub hle]
  congr 1
  rw [← Int.natCast_natAbs, Int.cast_natCast]

/-- Exponent combination for the kernel lattice sum (N6-i). -/
lemma bochnerKernel_exp_combine (h : ℝ) (hh : 0 < h)
    (N : ℕ) (hN : 1 ≤ N) (m : ℤ) (j l : Fin N) (r : ℕ) :
    cexp (↑(-(((j : ℝ) - (l : ℝ)) * h * bochnerNode h N r)) * Complex.I)
      * cexp (↑((m : ℝ) * h * bochnerNode h N r) * Complex.I)
      = cexp (↑(Real.pi * (((m - ((j : ℤ) - (l : ℤ)) : ℤ)) : ℝ)
        * ((r : ℝ) - (N : ℝ)) / (N : ℝ)) * Complex.I) := by
  have hNe : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNe' : h ≠ 0 := ne_of_gt hh
  have hNh : (N : ℝ) * h ≠ 0 := mul_ne_zero hNe hNe'
  have hξ : h * bochnerNode h N r
      = Real.pi * ((r : ℝ) - (N : ℝ)) / (N : ℝ) := by
    simp only [bochnerNode]
    field_simp
  have hcast : (m : ℝ) - ((j : ℝ) - (l : ℝ))
      = (((m - ((j : ℤ) - (l : ℤ)) : ℤ)) : ℝ) := by
    simp only [Int.cast_sub, Int.cast_natCast]
  have hmain : (-(((j : ℝ) - (l : ℝ)) * h * bochnerNode h N r)
      + (m : ℝ) * h * bochnerNode h N r)
      = Real.pi * (((m - ((j : ℤ) - (l : ℤ)) : ℤ)) : ℝ)
        * ((r : ℝ) - (N : ℝ)) / (N : ℝ) := by
    have hfac : (-(((j : ℝ) - (l : ℝ)) * h * bochnerNode h N r)
        + (m : ℝ) * h * bochnerNode h N r)
        = ((m : ℝ) - ((j : ℝ) - (l : ℝ))) * (h * bochnerNode h N r) := by
      ring
    rw [hfac, hcast, hξ]
    ring
  rw [← Complex.exp_add]
  congr 1
  rw [show (↑(-(((j : ℝ) - (l : ℝ)) * h * bochnerNode h N r)) * Complex.I
      + ↑((m : ℝ) * h * bochnerNode h N r) * Complex.I)
      = ↑(-(((j : ℝ) - (l : ℝ)) * h * bochnerNode h N r)
        + (m : ℝ) * h * bochnerNode h N r) * Complex.I from by
    push_cast
    ring]
  congr 1
  exact_mod_cast hmain

/-- Inner lattice sum for fixed `j, l` (N6-ii). -/
lemma bochnerKernel_inner_sum_eq (h : ℝ) (hh : 0 < h)
    (N : ℕ) (hN : 1 ≤ N) (m : ℤ) (hm : |m| ≤ (N : ℤ)) (j l : Fin N) :
    (∑ r ∈ Finset.range (2 * N),
      cexp (↑(-(((j : ℝ) - (l : ℝ)) * h * bochnerNode h N r)) * Complex.I)
        * cexp (↑((m : ℝ) * h * bochnerNode h N r) * Complex.I))
      = (if (j : ℤ) - (l : ℤ) = m then ((2 * N : ℕ) : ℂ) else 0) := by
  have hq : |m - ((j : ℤ) - (l : ℤ))| < 2 * (N : ℤ) := by
    have hj := j.2
    have hl := l.2
    have h1 : (j : ℤ) - (l : ℤ) ≤ (N : ℤ) - 1 := by omega
    have h2 : -((N : ℤ) - 1) ≤ (j : ℤ) - (l : ℤ) := by omega
    have hX : |(j : ℤ) - (l : ℤ)| ≤ (N : ℤ) - 1 := by
      rw [abs_le]
      exact ⟨h2, h1⟩
    have htri : |m - ((j : ℤ) - (l : ℤ))| ≤ |m| + |(j : ℤ) - (l : ℤ)| := by
      calc |m - ((j : ℤ) - (l : ℤ))| = |m + (-((j : ℤ) - (l : ℤ)))| := by
            rw [sub_eq_add_neg]
        _ ≤ |m| + |-((j : ℤ) - (l : ℤ))| := abs_add_le _ _
        _ = |m| + |(j : ℤ) - (l : ℤ)| := by rw [abs_neg]
    calc |m - ((j : ℤ) - (l : ℤ))| ≤ |m| + |(j : ℤ) - (l : ℤ)| := htri
      _ ≤ (N : ℤ) + ((N : ℤ) - 1) := add_le_add hm hX
      _ < 2 * (N : ℤ) := by linarith
  have hsum : (∑ r ∈ Finset.range (2 * N),
      cexp (↑(-(((j : ℝ) - (l : ℝ)) * h * bochnerNode h N r)) * Complex.I)
        * cexp (↑((m : ℝ) * h * bochnerNode h N r) * Complex.I))
      = ∑ r ∈ Finset.range (2 * N),
        cexp (↑(Real.pi * (((m - ((j : ℤ) - (l : ℤ)) : ℤ)) : ℝ)
          * ((r : ℝ) - (N : ℝ)) / (N : ℝ)) * Complex.I) :=
    Finset.sum_congr rfl
      (fun r _ => bochnerKernel_exp_combine h hh N hN m j l r)
  rw [hsum, sum_range_exp_pi_int_mul_div N hN (m - ((j : ℤ) - (l : ℤ))) hq]
  by_cases hc : (j : ℤ) - (l : ℤ) = m
  · rw [ite_eq_left (show m - ((j : ℤ) - (l : ℤ)) = 0 from by omega)]
    rw [ite_eq_left hc]
  · rw [ite_eq_right (show ¬(m - ((j : ℤ) - (l : ℤ)) = 0) from by omega)]
    rw [ite_eq_right hc]

/-- Collapse of the `(j, l)` sum onto the pair count (N6-iii). -/
lemma bochnerKernel_collapse {f : ℝ → ℂ} (h : ℝ) (N : ℕ) (m : ℤ)
    (hm : |m| ≤ (N : ℤ)) :
    (∑ j : Fin N, ∑ l : Fin N,
      f (((j : ℝ) - (l : ℝ)) * h)
        * (if (j : ℤ) - (l : ℤ) = m then ((2 * N : ℕ) : ℂ) else 0))
      = ((2 * N : ℕ) : ℂ) * ((N : ℂ) - (((|m| : ℤ)) : ℂ))
        * f ((m : ℝ) * h) := by
  have hterm3 : ∀ j l : Fin N,
      f (((j : ℝ) - (l : ℝ)) * h)
          * (if (j : ℤ) - (l : ℤ) = m then ((2 * N : ℕ) : ℂ) else 0)
        = f ((m : ℝ) * h)
          * (if (j : ℤ) - (l : ℤ) = m then ((2 * N : ℕ) : ℂ) else 0) := by
    intro j l
    by_cases hc : (j : ℤ) - (l : ℤ) = m
    · rw [ite_eq_left hc]
      have hX : ((j : ℝ) - (l : ℝ)) * h = (m : ℝ) * h := by
        congr 1
        exact_mod_cast hc
      rw [hX]
    · rw [ite_eq_right hc, mul_zero, mul_zero]
  have hI : ∀ j l : Fin N,
      (if (j : ℤ) - (l : ℤ) = m then ((2 * N : ℕ) : ℂ) else 0)
        = ((2 * N : ℕ) : ℂ)
          * (if (j : ℤ) - (l : ℤ) = m then (1 : ℂ) else 0) := by
    intro j l
    by_cases hc : (j : ℤ) - (l : ℤ) = m
    · rw [ite_eq_left hc, ite_eq_left hc, mul_one]
    · rw [ite_eq_right hc, ite_eq_right hc, mul_zero]
  calc (∑ j : Fin N, ∑ l : Fin N,
        f (((j : ℝ) - (l : ℝ)) * h)
          * (if (j : ℤ) - (l : ℤ) = m then ((2 * N : ℕ) : ℂ) else 0))
      = ∑ j : Fin N, ∑ l : Fin N,
        f ((m : ℝ) * h)
          * (if (j : ℤ) - (l : ℤ) = m then ((2 * N : ℕ) : ℂ) else 0) :=
        Finset.sum_congr rfl
          (fun j _ => Finset.sum_congr rfl (fun l _ => hterm3 j l))
    _ = f ((m : ℝ) * h) * ∑ j : Fin N, ∑ l : Fin N,
        (if (j : ℤ) - (l : ℤ) = m then ((2 * N : ℕ) : ℂ) else 0) := by
        simp only [← Finset.mul_sum]
    _ = f ((m : ℝ) * h) * (((2 * N : ℕ) : ℂ) * ∑ j : Fin N, ∑ l : Fin N,
        (if (j : ℤ) - (l : ℤ) = m then (1 : ℂ) else 0)) := by
        congr 1
        simp only [hI, ← Finset.mul_sum]
    _ = f ((m : ℝ) * h)
        * (((2 * N : ℕ) : ℂ) * ((N : ℂ) - (((|m| : ℤ)) : ℂ))) := by
        rw [sum_fin_pairs_sub_eq N m hm]
    _ = ((2 * N : ℕ) : ℂ) * ((N : ℂ) - (((|m| : ℤ)) : ℂ))
        * f ((m : ℝ) * h) := by
        ring

/-- Kernel lattice sum (N6). -/
lemma bochnerKernel_lattice_sum {f : ℝ → ℂ} (h : ℝ) (hh : 0 < h)
    (N : ℕ) (hN : 1 ≤ N) (m : ℤ) (hm : |m| ≤ (N : ℤ)) :
    (∑ r ∈ Finset.range (2 * N),
      bochnerKernel f h N (bochnerNode h N r)
        * cexp (↑((m : ℝ) * h * bochnerNode h N r) * Complex.I))
      = ((2 * N : ℕ) : ℂ) * ((N : ℂ) - (((|m| : ℤ)) : ℂ))
        * f ((m : ℝ) * h) := by
  have hexpand : ∀ r ∈ Finset.range (2 * N),
      bochnerKernel f h N (bochnerNode h N r)
          * cexp (↑((m : ℝ) * h * bochnerNode h N r) * Complex.I)
        = ∑ j : Fin N, ∑ l : Fin N,
          (f (((j : ℝ) - (l : ℝ)) * h)
            * cexp (↑(-(((j : ℝ) - (l : ℝ)) * h * bochnerNode h N r))
              * Complex.I))
            * cexp (↑((m : ℝ) * h * bochnerNode h N r) * Complex.I) := by
    intro r _
    simp only [bochnerKernel, Finset.sum_mul]
  have hswap (F : Fin N → Fin N → ℕ → ℂ) :
      (∑ r ∈ Finset.range (2 * N), ∑ j : Fin N, ∑ l : Fin N, F j l r)
        = ∑ j : Fin N, ∑ l : Fin N, ∑ r ∈ Finset.range (2 * N), F j l r := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
  have hjl : ∀ j l : Fin N,
      (∑ r ∈ Finset.range (2 * N),
        (f (((j : ℝ) - (l : ℝ)) * h)
          * cexp (↑(-(((j : ℝ) - (l : ℝ)) * h * bochnerNode h N r))
            * Complex.I))
          * cexp (↑((m : ℝ) * h * bochnerNode h N r) * Complex.I))
        = f (((j : ℝ) - (l : ℝ)) * h)
          * (if (j : ℤ) - (l : ℤ) = m then ((2 * N : ℕ) : ℂ) else 0) := by
    intro j l
    calc (∑ r ∈ Finset.range (2 * N),
          (f (((j : ℝ) - (l : ℝ)) * h)
            * cexp (↑(-(((j : ℝ) - (l : ℝ)) * h * bochnerNode h N r))
              * Complex.I))
            * cexp (↑((m : ℝ) * h * bochnerNode h N r) * Complex.I))
        = ∑ r ∈ Finset.range (2 * N),
          f (((j : ℝ) - (l : ℝ)) * h)
            * (cexp (↑(-(((j : ℝ) - (l : ℝ)) * h * bochnerNode h N r))
              * Complex.I)
              * cexp (↑((m : ℝ) * h * bochnerNode h N r) * Complex.I)) :=
          Finset.sum_congr rfl (fun r _ => by ring)
      _ = f (((j : ℝ) - (l : ℝ)) * h) * ∑ r ∈ Finset.range (2 * N),
          (cexp (↑(-(((j : ℝ) - (l : ℝ)) * h * bochnerNode h N r))
            * Complex.I)
            * cexp (↑((m : ℝ) * h * bochnerNode h N r) * Complex.I)) := by
          simp only [← Finset.mul_sum]
      _ = f (((j : ℝ) - (l : ℝ)) * h)
          * (if (j : ℤ) - (l : ℤ) = m then ((2 * N : ℕ) : ℂ) else 0) := by
          rw [bochnerKernel_inner_sum_eq h hh N hN m hm j l]
  calc (∑ r ∈ Finset.range (2 * N),
        bochnerKernel f h N (bochnerNode h N r)
          * cexp (↑((m : ℝ) * h * bochnerNode h N r) * Complex.I))
      = ∑ r ∈ Finset.range (2 * N), ∑ j : Fin N, ∑ l : Fin N,
        (f (((j : ℝ) - (l : ℝ)) * h)
          * cexp (↑(-(((j : ℝ) - (l : ℝ)) * h * bochnerNode h N r))
            * Complex.I))
          * cexp (↑((m : ℝ) * h * bochnerNode h N r) * Complex.I) :=
        Finset.sum_congr rfl (fun r hr => hexpand r hr)
    _ = ∑ j : Fin N, ∑ l : Fin N, ∑ r ∈ Finset.range (2 * N),
        (f (((j : ℝ) - (l : ℝ)) * h)
          * cexp (↑(-(((j : ℝ) - (l : ℝ)) * h * bochnerNode h N r))
            * Complex.I))
          * cexp (↑((m : ℝ) * h * bochnerNode h N r) * Complex.I) := hswap _
    _ = ∑ j : Fin N, ∑ l : Fin N,
        f (((j : ℝ) - (l : ℝ)) * h)
          * (if (j : ℤ) - (l : ℤ) = m then ((2 * N : ℕ) : ℂ) else 0) :=
        Finset.sum_congr rfl
          (fun j _ => Finset.sum_congr rfl (fun l _ => hjl j l))
    _ = ((2 * N : ℕ) : ℂ) * ((N : ℂ) - (((|m| : ℤ)) : ℂ))
        * f ((m : ℝ) * h) := bochnerKernel_collapse h N m hm

/-- Characteristic function of the approximation at lattice points (N8). -/
lemma charFun_bochnerApprox_lattice {f : ℝ → ℂ}
    (hpd : ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
      let S := ∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * f (x i - x j)
      S.im = 0 ∧ 0 ≤ S.re)
    (h : ℝ) (hh : 0 < h) (N : ℕ) (hN : 1 ≤ N) (m : ℤ) (hm : |m| ≤ (N : ℤ)) :
    charFun (bochnerApprox f h N) ((m : ℝ) * h)
      = (((N : ℂ) - (((|m| : ℤ)) : ℂ)) / (N : ℂ)) * f ((m : ℝ) * h) := by
  have hNeC : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hC : ((2 * N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * N ≠ 0)
  have hw : ∀ r ∈ Finset.range (2 * N), 0 ≤ bochnerWeight f h N r := by
    intro r _
    have hKre := (bochnerKernel_im_eq_zero_and_re_nonneg hpd h N
      (bochnerNode h N r)).2
    simp only [bochnerWeight]
    exact div_nonneg hKre (by positivity)
  have hKc : ∀ r ∈ Finset.range (2 * N),
      ((((bochnerKernel f h N (bochnerNode h N r)).re : ℝ)) : ℂ)
        = bochnerKernel f h N (bochnerNode h N r) := by
    intro r _
    have him := (bochnerKernel_im_eq_zero_and_re_nonneg hpd h N
      (bochnerNode h N r)).1
    apply Complex.ext
    · exact Complex.ofReal_re _
    · rw [Complex.ofReal_im]
      exact him.symm
  have hwC : ∀ r ∈ Finset.range (2 * N),
      (((bochnerWeight f h N r : ℝ)) : ℂ)
        = bochnerKernel f h N (bochnerNode h N r)
          / ((((2 * (N : ℝ) ^ 2 : ℝ))) : ℂ) := by
    intro r hr
    simp only [bochnerWeight, Complex.ofReal_div]
    rw [hKc r hr]
  have hexpm : ∀ r ∈ Finset.range (2 * N),
      cexp (↑((m : ℝ) * h) * ↑(bochnerNode h N r) * Complex.I)
        = cexp (↑((m : ℝ) * h * bochnerNode h N r) * Complex.I) := by
    intro r _
    congr 1
    push_cast
    ring
  have hD : ((((2 * (N : ℝ) ^ 2 : ℝ))) : ℂ)
      = ((2 * N : ℕ) : ℂ) * (N : ℂ) := by
    push_cast
    ring
  have hterm : ∀ r ∈ Finset.range (2 * N),
      (((bochnerWeight f h N r : ℝ)) : ℂ)
          * cexp (↑((m : ℝ) * h) * ↑(bochnerNode h N r) * Complex.I)
        = (1 / ((((2 * (N : ℝ) ^ 2 : ℝ))) : ℂ))
          * (bochnerKernel f h N (bochnerNode h N r)
            * cexp (↑((m : ℝ) * h * bochnerNode h N r) * Complex.I)) := by
    intro r hr
    rw [hwC r hr, hexpm r hr]
    ring
  simp only [bochnerApprox]
  rw [charFun_finsetSum_smul_dirac _ _ _ hw _]
  rw [show (∑ r ∈ Finset.range (2 * N),
      (((bochnerWeight f h N r : ℝ)) : ℂ)
        * cexp (↑((m : ℝ) * h) * ↑(bochnerNode h N r) * Complex.I))
      = (1 / ((((2 * (N : ℝ) ^ 2 : ℝ))) : ℂ)) * ∑ r ∈ Finset.range (2 * N),
        (bochnerKernel f h N (bochnerNode h N r)
          * cexp (↑((m : ℝ) * h * bochnerNode h N r) * Complex.I)) from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun r hr => hterm r hr)]
  rw [bochnerKernel_lattice_sum h hh N hN m hm, hD]
  have hCN : ((2 * N : ℕ) : ℂ) * (N : ℂ) ≠ 0 := mul_ne_zero hC hNeC
  field_simp

/-- The approximation is a probability measure supported in `[-π/h, π/h]` (N9). -/
lemma bochnerApprox_isProbabilityMeasure_and_support {f : ℝ → ℂ}
    (hpd : ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
      let S := ∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * f (x i - x j)
      S.im = 0 ∧ 0 ≤ S.re)
    (f0 : f 0 = 1) (h : ℝ) (hh : 0 < h) (N : ℕ) (hN : 1 ≤ N) :
    IsProbabilityMeasure (bochnerApprox f h N)
      ∧ ∀ᵐ x ∂(bochnerApprox f h N), |x| ≤ Real.pi / h := by
  have hNeC : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hw : ∀ r ∈ Finset.range (2 * N), 0 ≤ bochnerWeight f h N r := by
    intro r _
    have hKre := (bochnerKernel_im_eq_zero_and_re_nonneg hpd h N
      (bochnerNode h N r)).2
    simp only [bochnerWeight]
    exact div_nonneg hKre (by positivity)
  have hsum1 : ∑ r ∈ Finset.range (2 * N), bochnerWeight f h N r = 1 := by
    have h0h : (((0 : ℤ)) : ℝ) * h = 0 := by simp
    have hN80 := charFun_bochnerApprox_lattice hpd h hh N hN 0 (by simp)
    simp only [bochnerApprox] at hN80
    rw [h0h] at hN80
    have h70 := charFun_finsetSum_smul_dirac (Finset.range (2 * N))
      (bochnerNode h N) (bochnerWeight f h N) hw 0
    rw [h70] at hN80
    have hcexp0 : ∀ r ∈ Finset.range (2 * N),
        cexp (↑(0 : ℝ) * ↑(bochnerNode h N r) * Complex.I) = 1 := by
      intro r _
      have harg0 : (↑(0 : ℝ) * ↑(bochnerNode h N r) * Complex.I : ℂ) = 0 := by
        simp
      rw [harg0, Complex.exp_zero]
    have hLHS : (∑ r ∈ Finset.range (2 * N),
        (((bochnerWeight f h N r : ℝ)) : ℂ)
          * cexp (↑(0 : ℝ) * ↑(bochnerNode h N r) * Complex.I))
        = (((∑ r ∈ Finset.range (2 * N), bochnerWeight f h N r : ℝ)) : ℂ) := by
      rw [show (∑ r ∈ Finset.range (2 * N),
          (((bochnerWeight f h N r : ℝ)) : ℂ)
            * cexp (↑(0 : ℝ) * ↑(bochnerNode h N r) * Complex.I))
          = ∑ r ∈ Finset.range (2 * N),
            (((bochnerWeight f h N r : ℝ)) : ℂ) from
        Finset.sum_congr rfl (fun r hr => by rw [hcexp0 r hr, mul_one])]
      exact (Complex.ofReal_sum _ _).symm
    have hRHS : (((N : ℂ) - (((|(0 : ℤ)| : ℤ)) : ℂ)) / (N : ℂ))
        * f 0 = 1 := by
      rw [f0, mul_one, abs_zero, Int.cast_zero, sub_zero, div_self hNeC]
    rw [hLHS, hRHS] at hN80
    have hre := congrArg Complex.re hN80
    simpa using hre
  have hmass : (bochnerApprox f h N) Set.univ = 1 := by
    have h1 : (bochnerApprox f h N) Set.univ
        = ∑ r ∈ Finset.range (2 * N),
          ENNReal.ofReal (bochnerWeight f h N r) := by
      simp only [bochnerApprox, MeasureTheory.Measure.finsetSum_apply,
        MeasureTheory.Measure.smul_apply]
      apply Finset.sum_congr rfl
      intro r _
      rw [MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_univ _)]
      rw [smul_eq_mul, mul_one]
    rw [h1, ← ENNReal.ofReal_sum_of_nonneg hw, hsum1, ENNReal.ofReal_one]
  refine ⟨isProbabilityMeasure_iff.mpr hmass, ?_⟩
  have hmeas : MeasurableSet {x : ℝ | ¬|x| ≤ Real.pi / h} := by
    rw [show {x : ℝ | ¬|x| ≤ Real.pi / h}
        = (Set.Icc (-(Real.pi / h)) (Real.pi / h))ᶜ from by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_Icc, abs_le]]
    exact measurableSet_Icc.compl
  have hξ : ∀ r ∈ Finset.range (2 * N),
      |bochnerNode h N r| ≤ Real.pi / h := by
    intro r hr
    have hrN : r < 2 * N := Finset.mem_range.mp hr
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast (by omega : 0 < N)
    have hNh : (0 : ℝ) < (N : ℝ) * h := mul_pos hNpos hh
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
    have hr2 : (r : ℝ) < 2 * (N : ℝ) := by exact_mod_cast hrN
    have h1 : |(r : ℝ) - (N : ℝ)| ≤ (N : ℝ) := by
      rw [abs_le]
      constructor <;> linarith
    have hle : Real.pi * |(r : ℝ) - (N : ℝ)| ≤ Real.pi * (N : ℝ) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt Real.pi_pos)
    simp only [bochnerNode]
    rw [abs_div, abs_mul, abs_of_pos hNh, abs_of_pos Real.pi_pos]
    rw [div_le_div_iff₀ hNh hh]
    calc Real.pi * |(r : ℝ) - (N : ℝ)| * h
        ≤ Real.pi * (N : ℝ) * h :=
          mul_le_mul_of_nonneg_right hle (le_of_lt hh)
      _ = Real.pi * ((N : ℝ) * h) := by ring
  rw [ae_iff]
  simp only [bochnerApprox, MeasureTheory.Measure.finsetSum_apply]
  trans ∑ _r ∈ Finset.range (2 * N), (0 : ENNReal)
  · apply Finset.sum_congr rfl
    intro r hr
    rw [MeasureTheory.Measure.smul_apply, smul_eq_mul]
    have hmem : bochnerNode h N r ∉ {x : ℝ | ¬|x| ≤ Real.pi / h} := by
      simp only [Set.mem_ofPred_eq]
      exact not_not_intro (hξ r hr)
    have hdirac : Measure.dirac (bochnerNode h N r)
        {x : ℝ | ¬|x| ≤ Real.pi / h} = 0 := by
      rw [MeasureTheory.Measure.dirac_apply' _ hmeas]
      exact Set.indicator_of_notMem hmem _
    rw [hdirac, mul_zero]
  · simp

/-- Integrability of the characteristic-function integrand on a finite measure. -/
lemma integrable_exp_ofReal_mul (μ : Measure ℝ) [IsFiniteMeasure μ]
    (t : ℝ) :
    Integrable (fun y : ℝ => cexp (↑t * ↑y * Complex.I)) μ := by
  apply Integrable.of_bound (C := 1)
  · exact ((Complex.continuous_exp.comp
      ((continuous_const.mul continuous_ofReal).mul continuous_const)).aestronglyMeasurable)
  · filter_upwards with y
    rw [show (↑t * ↑y * Complex.I : ℂ) = ↑(t * y) * Complex.I by
      push_cast
      ring]
    rw [Complex.norm_exp_ofReal_mul_I]

/-- The characteristic-function integrand has norm 1. -/
lemma norm_cexp_ofReal_mul (a x : ℝ) :
    ‖cexp (↑a * ↑x * Complex.I)‖ = 1 := by
  rw [show (↑a * ↑x * Complex.I : ℂ) = ↑(a * x) * Complex.I by
    push_cast
    ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Pointwise modulus bound for `‖exp(sxI) - 1‖` (N10, pointwise part). -/
lemma norm_exp_sub_one_le_of_abs_le (h s x ε : ℝ) (hh : 0 < h)
    (hs : |s| ≤ h / 2) (hx : |x| ≤ Real.pi / h) (hε : 0 < ε) :
    ‖cexp (↑s * ↑x * Complex.I) - 1‖ ≤ ε + (1 - Real.cos (h * x)) / ε := by
  have hform : ∀ a b : ℝ, (↑a * ↑b * Complex.I : ℂ) = ↑(a * b) * Complex.I := by
    intro a b
    push_cast
    ring
  have hns : Complex.normSq (cexp (↑s * ↑x * Complex.I) - 1)
      = 2 - 2 * Real.cos (s * x) := by
    have hre : (cexp (↑s * ↑x * Complex.I) - 1).re
        = Real.cos (s * x) - 1 := by
      rw [hform, Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.one_re]
    have him : (cexp (↑s * ↑x * Complex.I) - 1).im
        = Real.sin (s * x) := by
      rw [hform, Complex.sub_im, Complex.exp_ofReal_mul_I_im, Complex.one_im,
        sub_zero]
    rw [Complex.normSq_apply, hre, him]
    linear_combination Real.sin_sq_add_cos_sq (s * x)
  have ha2 : ‖cexp (↑s * ↑x * Complex.I) - 1‖ ^ 2 ≤ (s * x) ^ 2 := by
    have hcos := Real.one_sub_sq_div_two_le_cos (x := s * x)
    rw [Complex.sq_norm, hns]
    linarith
  have hs2 : s ^ 2 ≤ h ^ 2 / 4 := by
    have hpair := abs_le.mp hs
    have e1 : (0 : ℝ) ≤ h / 2 - s := by linarith [hpair.1]
    have e2 : (0 : ℝ) ≤ h / 2 + s := by linarith [hpair.2]
    nlinarith [mul_nonneg e1 e2]
  have hmul : (s * x) ^ 2 ≤ (h * x) ^ 2 / 4 := by
    rw [mul_pow, mul_pow]
    have h3 := mul_le_mul_of_nonneg_right hs2 (sq_nonneg x)
    linarith
  have hhx : |h * x| ≤ Real.pi := by
    have hNe : h ≠ 0 := ne_of_gt hh
    rw [abs_mul, abs_of_pos hh]
    calc h * |x| ≤ h * (Real.pi / h) :=
          mul_le_mul_of_nonneg_left hx (le_of_lt hh)
      _ = Real.pi := by field_simp
  have hcos2 := Real.cos_le_one_sub_mul_cos_sq (x := h * x) hhx
  have hstep5 : (h * x) ^ 2 / 4 ≤ (Real.pi ^ 2 / 8) * (1 - Real.cos (h * x)) := by
    have h1 : (2 / Real.pi ^ 2) * (h * x) ^ 2 ≤ 1 - Real.cos (h * x) := by
      linarith [hcos2]
    have hpiNe : Real.pi ≠ 0 := Real.pi_ne_zero
    have h2 : (h * x) ^ 2 ≤ (Real.pi ^ 2 / 2) * (1 - Real.cos (h * x)) := by
      have hpos : (0 : ℝ) < Real.pi ^ 2 / 2 := by positivity
      have hmul2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hpos)
      rw [show (2 / Real.pi ^ 2) * (h * x) ^ 2 * (Real.pi ^ 2 / 2)
        = (h * x) ^ 2 from by field_simp] at hmul2
      linarith [hmul2]
    linarith [h2]
  have hpi4 : Real.pi ^ 2 ≤ 16 := by
    nlinarith [Real.pi_le_four, Real.pi_pos]
  have hcos1 : (0 : ℝ) ≤ 1 - Real.cos (h * x) := by
    linarith [Real.cos_le_one (h * x)]
  have h6 : (Real.pi ^ 2 / 8) * (1 - Real.cos (h * x))
      ≤ 2 * (1 - Real.cos (h * x)) := by
    have h78 : Real.pi ^ 2 / 8 ≤ 2 := by linarith [hpi4]
    exact mul_le_mul_of_nonneg_right h78 hcos1
  have ha2le : ‖cexp (↑s * ↑x * Complex.I) - 1‖ ^ 2
      ≤ 2 * (1 - Real.cos (h * x)) := by
    linarith [ha2, hmul, hstep5, h6]
  have hamgm : ‖cexp (↑s * ↑x * Complex.I) - 1‖
      ≤ ε + ‖cexp (↑s * ↑x * Complex.I) - 1‖ ^ 2 / (4 * ε) := by
    have hsq := sq_nonneg (‖cexp (↑s * ↑x * Complex.I) - 1‖ - 2 * ε)
    have h4ε : (0 : ℝ) < 4 * ε := by linarith
    have key : (‖cexp (↑s * ↑x * Complex.I) - 1‖ - ε) * (4 * ε)
        ≤ ‖cexp (↑s * ↑x * Complex.I) - 1‖ ^ 2 := by
      nlinarith [hsq]
    have hle : ‖cexp (↑s * ↑x * Complex.I) - 1‖ - ε
        ≤ ‖cexp (↑s * ↑x * Complex.I) - 1‖ ^ 2 / (4 * ε) :=
      (le_div_iff₀ h4ε).mpr key
    linarith
  have h7 : ‖cexp (↑s * ↑x * Complex.I) - 1‖ ^ 2 / (4 * ε)
      ≤ (1 - Real.cos (h * x)) / ε := by
    rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 4 * ε) hε]
    have hmul3 := mul_le_mul_of_nonneg_right ha2le (le_of_lt hε)
    have hnn := mul_nonneg hcos1 (le_of_lt hε)
    linarith [hmul3, hnn]
  linarith [hamgm, h7]

/-- Existence half of Lévy's continuity theorem on `ℝ` (N13). -/
lemma exists_charFun_eq_of_tendsto_charFun
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)]
    (g : ℝ → ℂ) (hg0 : ContinuousAt g 0)
    (hg : ∀ (t : ℝ), Filter.Tendsto (fun n => charFun (ν n) t) Filter.atTop (nhds (g t))) :
    ∃ (μ : Measure ℝ), IsProbabilityMeasure μ ∧ ∀ (t : ℝ), charFun μ t = g t := by
  have htight : IsTightMeasureSet (Set.range ν) :=
    isTightMeasureSet_of_tendsto_charFun hg0 hg
  classical
  let P : ℕ → ProbabilityMeasure ℝ := fun n => ⟨ν n, inferInstance⟩
  have hP : ∀ n, ((P n : ProbabilityMeasure ℝ) : Measure ℝ) = ν n := fun n => rfl
  have hS : {x : Measure ℝ | ∃ μ ∈ Set.range P, (μ : Measure ℝ) = x} = Set.range ν := by
    ext x
    constructor
    · rintro ⟨μ, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (hP n).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨P n, ⟨n, rfl⟩, hP n⟩
  have hcompact : IsCompact (closure (Set.range P)) := by
    apply isCompact_closure_of_isTightMeasureSet
    rw [hS]
    exact htight
  have hmem : ∀ n, P n ∈ closure (Set.range P) := fun n =>
    subset_closure (Set.mem_range_self n)
  obtain ⟨μ₀, _, φ, hφmono, hφlim⟩ := hcompact.tendsto_subseq hmem
  have hchar : ∀ (t : ℝ), Filter.Tendsto
      (fun n => charFun ((P (φ n) : ProbabilityMeasure ℝ) : Measure ℝ) t)
      Filter.atTop (nhds (charFun (μ₀ : Measure ℝ) t)) := by
    intro t
    have h := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hφlim) t
    simpa using h
  refine ⟨(μ₀ : Measure ℝ), inferInstance, fun t => ?_⟩
  have h1 := hchar t
  have h2 : Filter.Tendsto (fun n => charFun (ν (φ n)) t) Filter.atTop (nhds (g t)) :=
    (hg t).comp hφmono.tendsto_atTop
  have heq : (fun n => charFun ((P (φ n) : ProbabilityMeasure ℝ) : Measure ℝ) t)
      = (fun n => charFun (ν (φ n)) t) := by
    funext n
    rw [hP]
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

end Fourier.BochnerWanted
end
