/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.BoxIntegral.Integrability
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Tietze
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Order.LeftRightNhds
import Def.Analysis.Complex.LoomanMenchoff.Part5
/-!
# The Looman–Menchoff theorem

This file proves that a continuous complex-valued function with everywhere-existing partial
derivatives satisfying the Cauchy–Riemann equations is complex differentiable.
-/


namespace MetaMathlibExt

open Set Filter MeasureTheory Metric Finset

open BoxIntegral

open scoped ENNReal Interval NNReal Topology BoxIntegral Matrix

noncomputable section

theorem looman_rectBox_Icc (A B C D : ℝ) (hAB : A < B) (hCD : C < D) :
    Box.Icc (loomanRectBox A B C D hAB hCD) =
      {p | p 0 ∈ Icc A B ∧ p 1 ∈ Icc C D} := by
  ext p
  simp only [Box.Icc_def, Set.mem_Icc]
  constructor <;> rintro ⟨h₀, h₁⟩
  · exact ⟨⟨h₀ 0, h₁ 0⟩, h₀ 1, h₁ 1⟩
  · exact ⟨fun i ↦ by fin_cases i <;> simp_all [loomanRectBox],
      fun i ↦ by fin_cases i <;> simp_all [loomanRectBox]⟩

theorem looman_rectBox_boundary (f : ℂ → ℂ) (A B C D : ℝ)
    (hAB : A < B) (hCD : C < D) :
    loomanBoundary f (loomanRectBox A B C D hAB hCD) =
      loomanRectBoundary f A B C D := by
  rfl

theorem looman_dist_point_le (x y : ℝ) (z : ℂ) :
    dist (loomanPoint x y) z ≤ |x - z.re| + |y - z.im| := by
  rw [dist_eq_norm]
  have hsub : loomanPoint x y - z =
      (x - z.re : ℂ) + (y - z.im : ℂ) * Complex.I := by
    change (x : ℂ) + (y : ℂ) * Complex.I - z = _
    apply Complex.ext <;> simp
  rw [hsub]
  have hxnorm : ‖(x : ℂ) - (z.re : ℂ)‖ = |x - z.re| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hynorm : ‖(y : ℂ) - (z.im : ℂ)‖ = |y - z.im| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc
    ‖(x - z.re : ℂ) + (y - z.im : ℂ) * Complex.I‖ ≤
        ‖(x - z.re : ℂ)‖ + ‖(y - z.im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |x - z.re| + |y - z.im| := by
      rw [hxnorm, norm_mul, Complex.norm_I, mul_one, hynorm]

theorem looman_exists_baire_square {s C : Set ℂ} {P : C → Prop}
    (hs : IsOpen s) (hCs : C ⊆ s) {w : C}
    (hw : w ∈ interior {z : C | P z}) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∃ δ > 0,
      (∀ x y : ℝ, |x - (w : ℂ).re| ≤ 2 * δ → |y - (w : ℂ).im| ≤ 2 * δ →
        loomanPoint x y ∈ s) ∧
      (∀ z : C, |(z : ℂ).re - (w : ℂ).re| ≤ δ →
        |(z : ℂ).im - (w : ℂ).im| ≤ δ → P z) ∧
      2 * δ < r / (n + 1) := by
  obtain ⟨εP, hεP, hballP⟩ := Metric.isOpen_iff.1 isOpen_interior w hw
  obtain ⟨εs, hεs, hballs⟩ := Metric.isOpen_iff.1 hs (w : ℂ) (hCs w.property)
  let m := min εP (min εs (r / (n + 1)))
  have hm : 0 < m := by
    dsimp [m]
    exact lt_min hεP (lt_min hεs (div_pos hr (by positivity)))
  refine ⟨m / 8, by positivity, ?_, ?_, ?_⟩
  · intro x y hx hy
    apply hballs
    have hd := looman_dist_point_le x y (w : ℂ)
    calc
      dist (loomanPoint x y) (w : ℂ) ≤
          |x - (w : ℂ).re| + |y - (w : ℂ).im| := hd
      _ ≤ 4 * (m / 8) := by linarith
      _ < εs := by
        have hmle : m ≤ εs := le_trans (min_le_right _ _) (min_le_left _ _)
        linarith
  · intro z hx hy
    apply interior_subset (hballP ?_)
    have hd := looman_dist_point_le (z : ℂ).re (z : ℂ).im (w : ℂ)
    rw [show loomanPoint (z : ℂ).re (z : ℂ).im = (z : ℂ) by
      exact Complex.re_add_im (z : ℂ)] at hd
    calc
      dist z w ≤ |(z : ℂ).re - (w : ℂ).re| +
          |(z : ℂ).im - (w : ℂ).im| := hd
      _ ≤ 2 * (m / 8) := by linarith
      _ < εP := by
        have hmle : m ≤ εP := min_le_left _ _
        linarith
  · have hmle : m ≤ r / (n + 1) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    linarith

theorem looman_exists_continuous_extension {K : Set ℂ} (hK : IsClosed K)
    {f : ℂ → ℂ} (hf : ContinuousOn f K) :
    ∃ fe : ℂ → ℂ, Continuous fe ∧ EqOn fe f K := by
  let fK : C(K, ℂ) :=
    ⟨fun z ↦ f z, continuousOn_iff_continuous_domRestrict.mp hf⟩
  obtain ⟨fe, hfe⟩ := fK.exists_restrict_eq hK
  refine ⟨fe, fe.continuous, ?_⟩
  intro z hz
  have h := DFunLike.congr_fun hfe ⟨z, hz⟩
  exact h

set_option maxHeartbeats 1000000 in
-- The Baire and tagged-partition argument needs a larger elaboration budget.
/-- Looman–Menchoff theorem: a continuous complex function on a domain whose
partial derivatives exist everywhere and satisfy the Cauchy–Riemann equations
is holomorphic (differentiable in the complex sense).
Source: https://en.wikipedia.org/wiki/Looman%E2%80%93Menchoff_theorem
(statement id `looman-menchoff-s1`, canonical name "Looman-Menchoff theorem").

Proves `Wanted` entry `looman_menchoff`.

Proof: Baire category gives a square with uniform axis-wise Lipschitz bounds on the
exceptional set. A Goursat rectangle estimate and Morera's theorem eliminate that set.
-/
theorem looman_menchoff : ∀ {s : Set ℂ} {f : ℂ → ℂ} {ux uy vx vy : ℂ → ℝ},
    IsOpen s →
    ContinuousOn f s →
    (∀ z ∈ s, HasDerivAt (fun t : ℝ => (f (z + (t : ℂ))).re) (ux z) 0) →
    (∀ z ∈ s, HasDerivAt (fun t : ℝ => (f (z + (t : ℂ) * Complex.I)).re) (uy z) 0) →
    (∀ z ∈ s, HasDerivAt (fun t : ℝ => (f (z + (t : ℂ))).im) (vx z) 0) →
    (∀ z ∈ s, HasDerivAt (fun t : ℝ => (f (z + (t : ℂ) * Complex.I)).im) (vy z) 0) →
    (∀ z ∈ s, ux z = vy z) →
    (∀ z ∈ s, uy z = -(vx z)) →
    DifferentiableOn ℂ f s := by
  intro s f ux uy vx vy hs hf hux huy hvx hvy hcr₁ hcr₂ z₀ hz₀
  apply DifferentiableAt.differentiableWithinAt
  by_contra hz₀diff
  let H := loomanHolomorphicNeighborhood s f
  have hHopen : IsOpen H := looman_isOpen_holomorphicNeighborhood
  have hz₀H : z₀ ∉ H := fun hzH ↦
    hz₀diff (looman_differentiableAt_of_mem_holomorphicNeighborhood hzH)
  obtain ⟨R, hR, hballR⟩ := Metric.isOpen_iff.1 hs z₀ hz₀
  let ρ := R / 3
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρR : ρ < R := by dsimp [ρ]; linarith
  have h2ρR : 2 * ρ < R := by dsimp [ρ]; linarith
  let B := ball z₀ ρ
  let E := B ∩ Hᶜ
  have hBopen : IsOpen B := isOpen_ball
  have hEclosedPart : IsClosed Hᶜ := hHopen.isClosed_compl
  have hElc : IsLocallyClosed E := by
    exact hBopen.isLocallyClosed.inter hEclosedPart.isLocallyClosed
  let _ : LocallyCompactSpace E := hElc.locallyCompactSpace
  let _ : BaireSpace E := inferInstance
  have hEne : E.Nonempty := ⟨z₀, by exact ⟨mem_ball_self hρ, hz₀H⟩⟩
  have hBs : B ⊆ s := by
    intro z hz
    apply hballR
    exact hz.trans hρR
  have hEs : E ⊆ s := by
    intro z hz
    exact hBs hz.1
  have hshift : ∀ (n : ℕ) (z : ℂ), z ∈ E → ∀ h : ℝ,
      ‖h‖ < ρ / (n + 1) →
      z + (h : ℂ) ∈ s ∧ z + (h : ℂ) * Complex.I ∈ s := by
    intro n z hz h hh
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hhρ : ‖h‖ < ρ := hh.trans_le (div_le_self hρ.le (by linarith))
    have hzρ : dist z z₀ < ρ := by simpa [B] using hz.1
    constructor <;> apply hballR
    · calc
        dist (z + (h : ℂ)) z₀ ≤ dist (z + (h : ℂ)) z + dist z z₀ :=
          dist_triangle _ _ _
        _ = ‖h‖ + dist z z₀ := by rw [dist_eq_norm]; simp
        _ < 2 * ρ := by linarith
        _ < R := h2ρR
    · calc
        dist (z + (h : ℂ) * Complex.I) z₀ ≤
            dist (z + (h : ℂ) * Complex.I) z + dist z z₀ := dist_triangle _ _ _
        _ = ‖h‖ + dist z z₀ := by rw [dist_eq_norm]; simp
        _ < 2 * ρ := by linarith
        _ < R := h2ρR
  obtain ⟨n, hn⟩ := looman_baire_boundedAt hf hEne hEs hshift
    (fun z hz ↦ ⟨ux z + vx z * Complex.I,
      hasDerivAt_complex_of_re_im (hux z (hEs hz)) (hvx z (hEs hz))⟩)
    (fun z hz ↦ ⟨uy z + vy z * Complex.I,
      hasDerivAt_complex_of_re_im (huy z (hEs hz)) (hvy z (hEs hz))⟩)
  rcases hn with ⟨w, hw⟩
  obtain ⟨δ, hδ, houterB, hinnerBounded, hside⟩ :=
    looman_exists_baire_square hBopen inter_subset_left hw hρ n
  let K : Set ℂ := Icc ((w : ℂ).re - 2 * δ) ((w : ℂ).re + 2 * δ) ×ℂ
    Icc ((w : ℂ).im - 2 * δ) ((w : ℂ).im + 2 * δ)
  have hKclosed : IsClosed K := isClosed_Icc.reProdIm isClosed_Icc
  have hKs : K ⊆ s := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    apply hBs
    have hzB := houterB z.re z.im (by
      rw [abs_le]
      constructor <;> linarith [hz.1.1, hz.1.2]) (by
      rw [abs_le]
      constructor <;> linarith [hz.2.1, hz.2.2])
    simpa only [loomanPoint, Complex.re_add_im] using hzB
  obtain ⟨fe, hfecont, hfe⟩ :=
    looman_exists_continuous_extension hKclosed (hf.mono hKs)
  let A := (w : ℂ).re - δ
  let B₁ := (w : ℂ).re + δ
  let C := (w : ℂ).im - δ
  let D := (w : ℂ).im + δ
  have hAB : A < B₁ := by dsimp [A, B₁]; linarith
  have hCD : C < D := by dsimp [C, D]; linarith
  let I := loomanRectBox A B₁ C D hAB hCD
  let F : Set (Fin 2 → ℝ) := loomanCoordPoint ⁻¹' Hᶜ
  have hFclosed : IsClosed F := hHopen.isClosed_compl.preimage (by
    unfold loomanCoordPoint loomanPoint
    fun_prop)
  have hfe_eq_nhds {z : ℂ} (hzre : z.re ∈ Icc A B₁) (hzim : z.im ∈ Icc C D) :
      fe =ᶠ[nhds z] f := by
    have hzopen : z ∈ Ioo ((w : ℂ).re - 2 * δ) ((w : ℂ).re + 2 * δ) ×ℂ
        Ioo ((w : ℂ).im - 2 * δ) ((w : ℂ).im + 2 * δ) := by
      rw [Complex.mem_reProdIm]
      dsimp [A, B₁, C, D] at hzre hzim
      constructor <;> constructor <;> linarith [hzre.1, hzre.2, hzim.1, hzim.2]
    filter_upwards [((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hzopen)] with y hy
    apply hfe
    rw [Complex.mem_reProdIm] at hy ⊢
    exact ⟨⟨hy.1.1.le, hy.1.2.le⟩, hy.2.1.le, hy.2.2.le⟩
  have hr_exists (x : Fin 2 → ℝ) : ∃ r > 0,
      x ∈ Box.Icc I → x ∉ F →
        ∀ y ∈ closedBall x r, DifferentiableAt ℂ f (loomanCoordPoint y) := by
    by_cases hx : x ∈ Box.Icc I ∧ x ∉ F
    · have hxH : loomanCoordPoint x ∈ H := by simpa [F] using hx.2
      rcases hxH with ⟨t, htopen, hxt, -, hdifft⟩
      have hpreopen : IsOpen (loomanCoordPoint ⁻¹' t) := htopen.preimage (by
        unfold loomanCoordPoint loomanPoint
        fun_prop)
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hpreopen x hxt
      refine ⟨r / 2, by positivity, fun _ _ y hy ↦ ?_⟩
      apply (hdifft (loomanCoordPoint y) ?_).differentiableAt
        (htopen.mem_nhds ?_)
      · apply hball
        rw [mem_ball]
        exact (mem_closedBall.1 hy).trans_lt (by linarith)
      · apply hball
        rw [mem_ball]
        exact (mem_closedBall.1 hy).trans_lt (by linarith)
    · refine ⟨1, zero_lt_one, fun hxI hxF ↦ ?_⟩
      exact (hx ⟨hxI, hxF⟩).elim
  choose r₀ hr₀ hdiff_r₀ using hr_exists
  let gauge : (Fin 2 → ℝ) → Ioi (0 : ℝ) := fun x ↦ ⟨r₀ x, hr₀ x⟩
  have hbox (J : Box (Fin 2)) (hJI : J ≤ I) : loomanBoundary fe J = 0 := by
    let g := loomanBoundary_boxAdditive fe hfecont J
    have hCnonneg : 0 ≤ (4 + 16 * (J.distortion : ℝ)) * (n + 1) := by positivity
    have hg : g J = 0 := looman_boxAdditive_eq_zero hFclosed g hCnonneg gauge (by
      intro x hxJ hxF L hLJ hLball
      change loomanBoundary fe L = 0
      change loomanRectBoundary fe (L.lower 0) (L.upper 0) (L.lower 1) (L.upper 1) = 0
      apply looman_rectBoundary_eq_zero_of_differentiableOn
        (L.lower_lt_upper 0).le (L.lower_lt_upper 1).le hfecont
      intro a ha b hb
      let y : Fin 2 → ℝ := ![a, b]
      have hyL : y ∈ Box.Icc L := by
        rw [Box.Icc_def]
        exact ⟨fun i ↦ by fin_cases i <;> simp [y, ha.1.le, hb.1.le],
          fun i ↦ by fin_cases i <;> simp [y, ha.2.le, hb.2.le]⟩
      have hyI : y ∈ Box.Icc I := Box.le_iff_Icc.1 (hLJ.trans hJI) hyL
      have hycoords : y 0 ∈ Icc A B₁ ∧ y 1 ∈ Icc C D := by
        simpa [I, looman_rectBox_Icc] using hyI
      have hfdiff : DifferentiableAt ℂ f (loomanCoordPoint y) :=
        hdiff_r₀ x (Box.le_iff_Icc.1 hJI hxJ) hxF y (hLball hyL)
      have hyre : (loomanCoordPoint y).re = y 0 := by
        unfold loomanCoordPoint loomanPoint
        simp
      have hyim : (loomanCoordPoint y).im = y 1 := by
        unfold loomanCoordPoint loomanPoint
        simp
      have heq : fe =ᶠ[nhds (loomanCoordPoint y)] f := hfe_eq_nhds
        (by rw [hyre]; exact hycoords.1) (by rw [hyim]; exact hycoords.2)
      simpa [loomanCoordPoint, loomanPoint, y] using
        hfdiff.congr_of_eventuallyEq heq) (by
      intro L hLJ hdist x hxL hxF
      let toVec : ℝ × ℝ → Fin 2 → ℝ := fun p ↦ ![p.1, p.2]
      let rect : Set (ℝ × ℝ) :=
        Icc (L.lower 0) (L.upper 0) ×ˢ Icc (L.lower 1) (L.upper 1)
      let bad : Set (ℝ × ℝ) := toVec ⁻¹' F
      let FL : Set (ℝ × ℝ) := rect ∩ bad
      have hbadclosed : IsClosed bad := hFclosed.preimage (by
        unfold toVec
        fun_prop)
      have hrectcompact : IsCompact rect := isCompact_Icc.prod isCompact_Icc
      have hFLcompact : IsCompact FL := hrectcompact.inter_right hbadclosed
      have hxvec : toVec (x 0, x 1) = x := by
        funext i
        fin_cases i <;> rfl
      have hxrect : (x 0, x 1) ∈ rect := by
        change x 0 ∈ Icc (L.lower 0) (L.upper 0) ∧
          x 1 ∈ Icc (L.lower 1) (L.upper 1)
        rw [Box.Icc_def] at hxL
        exact ⟨⟨hxL.1 0, hxL.2 0⟩, hxL.1 1, hxL.2 1⟩
      have hFLne : FL.Nonempty := ⟨(x 0, x 1), hxrect, by
        change toVec (x 0, x 1) ∈ F
        rwa [hxvec]⟩
      have hFLsub : FL ⊆ rect := inter_subset_left
      have hbounded (p : ℝ × ℝ) (hp : p ∈ FL) :
          loomanBoundedAt f ρ n (loomanPoint p.1 p.2) := by
        have hqL : toVec p ∈ Box.Icc L := by
          rw [Box.Icc_def]
          constructor
          · intro i
            fin_cases i
            · exact hp.1.1.1
            · exact hp.1.2.1
          · intro i
            fin_cases i
            · exact hp.1.1.2
            · exact hp.1.2.2
        have hqI : toVec p ∈ Box.Icc I :=
          Box.le_iff_Icc.1 (hLJ.trans hJI) hqL
        have hqcoords : toVec p 0 ∈ Icc A B₁ ∧ toVec p 1 ∈ Icc C D := by
          simpa [I, looman_rectBox_Icc] using hqI
        have hpH : loomanPoint p.1 p.2 ∉ H := by
          have : toVec p ∈ F := hp.2
          simpa [F, loomanCoordPoint, loomanPoint, toVec] using this
        have hpabsx : |p.1 - (w : ℂ).re| ≤ δ := by
          have hlo := hqcoords.1.1
          have hhi := hqcoords.1.2
          dsimp [A, B₁, toVec] at hlo hhi
          rw [abs_le]
          constructor <;> linarith
        have hpabsy : |p.2 - (w : ℂ).im| ≤ δ := by
          have hlo := hqcoords.2.1
          have hhi := hqcoords.2.2
          dsimp [C, D, toVec] at hlo hhi
          rw [abs_le]
          constructor <;> linarith
        have hpB : loomanPoint p.1 p.2 ∈ B := houterB p.1 p.2
          (hpabsx.trans (by linarith)) (hpabsy.trans (by linarith))
        apply hinnerBounded ⟨loomanPoint p.1 p.2, hpB, hpH⟩
        · simpa [loomanPoint] using hpabsx
        · simpa [loomanPoint] using hpabsy
      have hLx : L.upper 0 - L.lower 0 ≤ dist L.lower L.upper := by
        have hd := dist_le_pi_dist L.lower L.upper 0
        calc
          L.upper 0 - L.lower 0 = |L.lower 0 - L.upper 0| := by
            rw [abs_of_neg (sub_neg.mpr (L.lower_lt_upper 0))]
            ring
          _ ≤ dist L.lower L.upper := by simpa [Real.dist_eq] using hd
      have hLy : L.upper 1 - L.lower 1 ≤ dist L.lower L.upper := by
        have hd := dist_le_pi_dist L.lower L.upper 1
        calc
          L.upper 1 - L.lower 1 = |L.lower 1 - L.upper 1| := by
            rw [abs_of_neg (sub_neg.mpr (L.lower_lt_upper 1))]
            ring
          _ ≤ dist L.lower L.upper := by simpa [Real.dist_eq] using hd
      have hLheight : dist L.lower L.upper ≤
          (J.distortion : ℝ) * (L.upper 1 - L.lower 1) := by
        calc
          dist L.lower L.upper ≤
              (L.distortion : ℝ) * (L.upper 1 - L.lower 1) :=
            L.dist_le_distortion_mul 1
          _ ≤ (J.distortion : ℝ) * (L.upper 1 - L.lower 1) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast hdist
            · exact sub_nonneg.mpr (L.lower_lt_upper 1).le
      have hLwidth : dist L.lower L.upper ≤
          (J.distortion : ℝ) * (L.upper 0 - L.lower 0) := by
        calc
          dist L.lower L.upper ≤
              (L.distortion : ℝ) * (L.upper 0 - L.lower 0) :=
            L.dist_le_distortion_mul 0
          _ ≤ (J.distortion : ℝ) * (L.upper 0 - L.lower 0) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast hdist
            · exact sub_nonneg.mpr (L.lower_lt_upper 0).le
      have hhol : ∀ a ∈ Ioo (L.lower 0) (L.upper 0),
          ∀ b ∈ Ioo (L.lower 1) (L.upper 1), (a, b) ∉ FL →
            DifferentiableAt ℂ fe (loomanPoint a b) := by
        intro a ha b hb hpFL
        let q : Fin 2 → ℝ := ![a, b]
        have hqL : q ∈ Box.Icc L := by
          rw [Box.Icc_def]
          exact ⟨fun i ↦ by fin_cases i <;> simp [q, ha.1.le, hb.1.le],
            fun i ↦ by fin_cases i <;> simp [q, ha.2.le, hb.2.le]⟩
        have hqI : q ∈ Box.Icc I := Box.le_iff_Icc.1 (hLJ.trans hJI) hqL
        have hqcoords : q 0 ∈ Icc A B₁ ∧ q 1 ∈ Icc C D := by
          simpa [I, looman_rectBox_Icc] using hqI
        have hnotF : q ∉ F := by
          intro hqF
          apply hpFL
          exact ⟨⟨⟨ha.1.le, ha.2.le⟩, hb.1.le, hb.2.le⟩, hqF⟩
        have hpointH : loomanPoint a b ∈ H := by
          simpa [F, loomanCoordPoint, loomanPoint, q] using hnotF
        have hfdiff :=
          looman_differentiableAt_of_mem_holomorphicNeighborhood hpointH
        have heq : fe =ᶠ[nhds (loomanPoint a b)] f := hfe_eq_nhds
          (by
            rw [show (loomanPoint a b).re = a by unfold loomanPoint; simp]
            simpa [q] using hqcoords.1)
          (by
            rw [show (loomanPoint a b).im = b by unfold loomanPoint; simp]
            simpa [q] using hqcoords.2)
        exact hfdiff.congr_of_eventuallyEq heq
      have hmain (p : ℝ × ℝ) (hp : p ∈ FL) :
          p.1 ∈ Icc A B₁ ∧ p.2 ∈ Icc C D := by
        have hqL : toVec p ∈ Box.Icc L := by
          rw [Box.Icc_def]
          constructor
          · intro i
            fin_cases i
            · exact hp.1.1.1
            · exact hp.1.2.1
          · intro i
            fin_cases i
            · exact hp.1.1.2
            · exact hp.1.2.2
        have hqI := Box.le_iff_Icc.1 (hLJ.trans hJI) hqL
        have hcoords : toVec p 0 ∈ Icc A B₁ ∧ toVec p 1 ∈ Icc C D := by
          simpa [I, looman_rectBox_Icc] using hqI
        simpa [toVec] using hcoords
      have hpointS (p : ℝ × ℝ) (hp : p ∈ FL) : loomanPoint p.1 p.2 ∈ s := by
        have hm := hmain p hp
        apply hBs
        apply houterB p.1 p.2
        · rw [abs_le]
          dsimp [A, B₁] at hm
          constructor <;> linarith [hm.1.1, hm.1.2]
        · rw [abs_le]
          dsimp [C, D] at hm
          constructor <;> linarith [hm.2.1, hm.2.2]
      have heqpoint (p : ℝ × ℝ) (hp : p ∈ FL) :
          fe =ᶠ[nhds (loomanPoint p.1 p.2)] f := by
        have hm := hmain p hp
        apply hfe_eq_nhds
        · rw [show (loomanPoint p.1 p.2).re = p.1 by unfold loomanPoint; simp]
          exact hm.1
        · rw [show (loomanPoint p.1 p.2).im = p.2 by unfold loomanPoint; simp]
          exact hm.2
      have transfer_x (p : ℝ × ℝ) (hp : p ∈ FL) (c : ℂ → ℝ) (a : ℝ)
          (hbase₀ : HasDerivAt
            (fun t : ℝ ↦ c (f (loomanPoint p.1 p.2 + (t : ℂ)))) a 0) :
          HasDerivAt (fun x ↦ c (fe (loomanPoint x p.2))) a p.1 := by
        have houter : HasDerivAt
            (fun t : ℝ ↦ c (f (loomanPoint p.1 p.2 + (t : ℂ))))
            a (p.1 - p.1) := by
          simpa using hbase₀
        have hinner : HasDerivAt (fun x : ℝ ↦ x - p.1) 1 p.1 := by
          simpa only [id_eq] using (hasDerivAt_id p.1).sub_const p.1
        have hbase := houter.comp (h := fun x : ℝ ↦ x - p.1) p.1 hinner
        have hfline : HasDerivAt (fun x ↦ c (f (loomanPoint x p.2))) a p.1 := by
          convert hbase using 1
          · funext x
            congr 2
            unfold loomanPoint
            push_cast
            ring
          · simp
        have heqline : (fun x ↦ c (fe (loomanPoint x p.2))) =ᶠ[nhds p.1]
            fun x ↦ c (f (loomanPoint x p.2)) := by
          have htend : Tendsto (fun x : ℝ ↦ loomanPoint x p.2) (nhds p.1)
              (nhds (loomanPoint p.1 p.2)) := by
            apply Continuous.continuousAt
            unfold loomanPoint
            fun_prop
          filter_upwards [(heqpoint p hp).comp_tendsto htend] with x hx
          exact congrArg c hx
        exact hfline.congr_of_eventuallyEq heqline
      have transfer_y (p : ℝ × ℝ) (hp : p ∈ FL) (c : ℂ → ℝ) (a : ℝ)
          (hbase₀ : HasDerivAt
            (fun t : ℝ ↦ c (f (loomanPoint p.1 p.2 + (t : ℂ) * Complex.I))) a 0) :
          HasDerivAt (fun y ↦ c (fe (loomanPoint p.1 y))) a p.2 := by
        have houter : HasDerivAt
            (fun t : ℝ ↦ c (f (loomanPoint p.1 p.2 + (t : ℂ) * Complex.I)))
            a (p.2 - p.2) := by
          simpa using hbase₀
        have hinner : HasDerivAt (fun y : ℝ ↦ y - p.2) 1 p.2 := by
          simpa only [id_eq] using (hasDerivAt_id p.2).sub_const p.2
        have hbase := houter.comp (h := fun y : ℝ ↦ y - p.2) p.2 hinner
        have hfline : HasDerivAt (fun y ↦ c (f (loomanPoint p.1 y))) a p.2 := by
          convert hbase using 1
          · funext y
            congr 2
            unfold loomanPoint
            push_cast
            ring
          · simp
        have heqline : (fun y ↦ c (fe (loomanPoint p.1 y))) =ᶠ[nhds p.2]
            fun y ↦ c (f (loomanPoint p.1 y)) := by
          have htend : Tendsto (fun y : ℝ ↦ loomanPoint p.1 y) (nhds p.2)
              (nhds (loomanPoint p.1 p.2)) := by
            apply Continuous.continuousAt
            unfold loomanPoint
            fun_prop
          filter_upwards [(heqpoint p hp).comp_tendsto htend] with y hy
          exact congrArg c hy
        exact hfline.congr_of_eventuallyEq heqline
      have hux_fe (p : ℝ × ℝ) (hp : p ∈ FL) :
          HasDerivAt (fun x ↦ (fe (loomanPoint x p.2)).re)
            (ux (loomanPoint p.1 p.2)) p.1 :=
        transfer_x p hp Complex.re (ux (loomanPoint p.1 p.2))
          (hux (loomanPoint p.1 p.2) (hpointS p hp))
      have huy_fe (p : ℝ × ℝ) (hp : p ∈ FL) :
          HasDerivAt (fun y ↦ (fe (loomanPoint p.1 y)).re)
            (uy (loomanPoint p.1 p.2)) p.2 :=
        transfer_y p hp Complex.re (uy (loomanPoint p.1 p.2))
          (huy (loomanPoint p.1 p.2) (hpointS p hp))
      have hvx_fe (p : ℝ × ℝ) (hp : p ∈ FL) :
          HasDerivAt (fun x ↦ (fe (loomanPoint x p.2)).im)
            (vx (loomanPoint p.1 p.2)) p.1 :=
        transfer_x p hp Complex.im (vx (loomanPoint p.1 p.2))
          (hvx (loomanPoint p.1 p.2) (hpointS p hp))
      have hvy_fe (p : ℝ × ℝ) (hp : p ∈ FL) :
          HasDerivAt (fun y ↦ (fe (loomanPoint p.1 y)).im)
            (vy (loomanPoint p.1 p.2)) p.2 :=
        transfer_y p hp Complex.im (vy (loomanPoint p.1 p.2))
          (hvy (loomanPoint p.1 p.2) (hpointS p hp))
      have hKpos : 0 < ρ / (n + 1) := div_pos hρ (by positivity)
      have hlipx (p : ℝ × ℝ) (hp : p ∈ FL) :
          ∀ᶠ (t : ℝ) in nhds 0,
            ‖f (loomanPoint p.1 p.2 + (t : ℂ)) -
                f (loomanPoint p.1 p.2 + (0 : ℂ))‖ ≤ (n + 1) * ‖t‖ := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hKpos] with t ht
        simpa using (hbounded p hp t (by simpa [Real.dist_eq] using ht)).1
      have hlipy (p : ℝ × ℝ) (hp : p ∈ FL) :
          ∀ᶠ (t : ℝ) in nhds 0,
            ‖f (loomanPoint p.1 p.2 + (t : ℂ) * Complex.I) -
                f (loomanPoint p.1 p.2 + (0 : ℂ) * Complex.I)‖ ≤
              (n + 1) * ‖t‖ := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hKpos] with t ht
        simpa using (hbounded p hp t (by simpa [Real.dist_eq] using ht)).2
      have huxK (p : ℝ × ℝ) (hp : p ∈ FL) :
          |ux (loomanPoint p.1 p.2)| ≤ (n : ℝ) + 1 :=
        looman_abs_deriv_re_le_of_norm_sub_le
          (hux (loomanPoint p.1 p.2) (hpointS p hp)) (by positivity) (hlipx p hp)
      have huyK (p : ℝ × ℝ) (hp : p ∈ FL) :
          |uy (loomanPoint p.1 p.2)| ≤ (n : ℝ) + 1 :=
        looman_abs_deriv_re_le_of_norm_sub_le
          (huy (loomanPoint p.1 p.2) (hpointS p hp)) (by positivity) (hlipy p hp)
      have hvxK (p : ℝ × ℝ) (hp : p ∈ FL) :
          |vx (loomanPoint p.1 p.2)| ≤ (n : ℝ) + 1 :=
        looman_abs_deriv_im_le_of_norm_sub_le
          (hvx (loomanPoint p.1 p.2) (hpointS p hp)) (by positivity) (hlipx p hp)
      have hvyK (p : ℝ × ℝ) (hp : p ∈ FL) :
          |vy (loomanPoint p.1 p.2)| ≤ (n : ℝ) + 1 :=
        looman_abs_deriv_im_le_of_norm_sub_le
          (hvy (loomanPoint p.1 p.2) (hpointS p hp)) (by positivity) (hlipy p hp)
      have hLIbounds := Box.le_iff_bounds.1 (hLJ.trans hJI)
      have hLipX (p : ℝ × ℝ) (hp : p ∈ FL) (a : ℝ)
          (ha : a ∈ Icc (L.lower 0) (L.upper 0)) :
          ‖fe (loomanPoint a p.2) - fe (loomanPoint p.1 p.2)‖ ≤
            (n + 1) * |a - p.1| := by
        have hpmain := hmain p hp
        have hamain : a ∈ Icc A B₁ := by
          constructor
          · calc
              A = I.lower 0 := by rfl
              _ ≤ L.lower 0 := hLIbounds.1 0
              _ ≤ a := ha.1
          · calc
              a ≤ L.upper 0 := ha.2
              _ ≤ I.upper 0 := hLIbounds.2 0
              _ = B₁ := by rfl
        have hsmall : ‖a - p.1‖ < ρ / (n + 1) := by
          have habs : |a - p.1| ≤ 2 * δ := by
            rw [abs_le]
            dsimp [A, B₁] at hamain hpmain
            constructor <;> linarith [hamain.1, hamain.2, hpmain.1.1, hpmain.1.2]
          simpa [Real.norm_eq_abs] using habs.trans_lt hside
        have hb := (hbounded p hp (a - p.1) hsmall).1
        have hfea : fe (loomanPoint a p.2) = f (loomanPoint a p.2) :=
          (hfe_eq_nhds
            (by
              rw [show (loomanPoint a p.2).re = a by unfold loomanPoint; simp]
              exact hamain)
            (by
              rw [show (loomanPoint a p.2).im = p.2 by unfold loomanPoint; simp]
              exact hpmain.2)).self_of_nhds
        have hfep : fe (loomanPoint p.1 p.2) = f (loomanPoint p.1 p.2) :=
          (heqpoint p hp).self_of_nhds
        rw [hfea, hfep]
        have hadd : loomanPoint p.1 p.2 + ((a - p.1 : ℝ) : ℂ) =
            loomanPoint a p.2 := by
          unfold loomanPoint
          push_cast
          ring
        simpa only [hadd, add_zero, Real.norm_eq_abs] using hb
      have hLipY (p : ℝ × ℝ) (hp : p ∈ FL) (b : ℝ)
          (hbmem : b ∈ Icc (L.lower 1) (L.upper 1)) :
          ‖fe (loomanPoint p.1 b) - fe (loomanPoint p.1 p.2)‖ ≤
            (n + 1) * |b - p.2| := by
        have hpmain := hmain p hp
        have hbmain : b ∈ Icc C D := by
          constructor
          · calc
              C = I.lower 1 := by rfl
              _ ≤ L.lower 1 := hLIbounds.1 1
              _ ≤ b := hbmem.1
          · calc
              b ≤ L.upper 1 := hbmem.2
              _ ≤ I.upper 1 := hLIbounds.2 1
              _ = D := by rfl
        have hsmall : ‖b - p.2‖ < ρ / (n + 1) := by
          have habs : |b - p.2| ≤ 2 * δ := by
            rw [abs_le]
            dsimp [C, D] at hbmain hpmain
            constructor <;> linarith [hbmain.1, hbmain.2, hpmain.2.1, hpmain.2.2]
          simpa [Real.norm_eq_abs] using habs.trans_lt hside
        have hb := (hbounded p hp (b - p.2) hsmall).2
        have hfeb : fe (loomanPoint p.1 b) = f (loomanPoint p.1 b) :=
          (hfe_eq_nhds
            (by
              rw [show (loomanPoint p.1 b).re = p.1 by unfold loomanPoint; simp]
              exact hpmain.1)
            (by
              rw [show (loomanPoint p.1 b).im = b by unfold loomanPoint; simp]
              exact hbmain)).self_of_nhds
        have hfep : fe (loomanPoint p.1 p.2) = f (loomanPoint p.1 p.2) :=
          (heqpoint p hp).self_of_nhds
        rw [hfeb, hfep]
        have hadd : loomanPoint p.1 p.2 + ((b - p.2 : ℝ) : ℂ) * Complex.I =
            loomanPoint p.1 b := by
          unfold loomanPoint
          push_cast
          ring
        simpa only [hadd, sub_self, Complex.ofReal_zero, zero_mul, add_zero,
          Real.norm_eq_abs] using hb
      have hestimate := looman_rectBoundary_norm_le
        (f := fe) (F := FL)
        (A := L.lower 0) (B := L.upper 0) (C := L.lower 1) (D := L.upper 1)
        (K := (n : ℝ) + 1) (L := dist L.lower L.upper)
        (κ := (J.distortion : ℝ))
        (ux := fun p ↦ ux (loomanPoint p.1 p.2))
        (uy := fun p ↦ uy (loomanPoint p.1 p.2))
        (vx := fun p ↦ vx (loomanPoint p.1 p.2))
        (vy := fun p ↦ vy (loomanPoint p.1 p.2))
        (L.lower_lt_upper 0) (L.lower_lt_upper 1) (by positivity) (by positivity)
        hLx hLy hLheight hLwidth hfecont hFLcompact hFLne hFLsub hhol
        hux_fe huy_fe hvx_fe hvy_fe huxK huyK hvxK hvyK
        (fun p hp ↦ hcr₁ (loomanPoint p.1 p.2) (hpointS p hp))
        (fun p hp ↦ hcr₂ (loomanPoint p.1 p.2) (hpointS p hp))
        hLipX hLipY
      have hpre : MeasurableEquiv.finTwoArrow ⁻¹' (rect \ FL) =
          Box.Icc L \ F := by
        ext q
        have hvec : toVec (q 0, q 1) = q := by
          funext i
          fin_cases i <;> rfl
        have hrect_iff : (q 0, q 1) ∈ rect ↔ q ∈ Box.Icc L := by
          rw [Box.Icc_def]
          change (q 0 ∈ Icc (L.lower 0) (L.upper 0) ∧
            q 1 ∈ Icc (L.lower 1) (L.upper 1)) ↔ _
          constructor
          · rintro ⟨h₀, h₁⟩
            exact ⟨fun i ↦ by fin_cases i <;> simp_all,
              fun i ↦ by fin_cases i <;> simp_all⟩
          · rintro ⟨hl, hu⟩
            exact ⟨⟨hl 0, hu 0⟩, hl 1, hu 1⟩
        have hbad_iff : (q 0, q 1) ∈ bad ↔ q ∈ F := by
          change toVec (q 0, q 1) ∈ F ↔ q ∈ F
          rw [hvec]
        change ((q 0, q 1) ∈ rect ∧ (q 0, q 1) ∉ FL) ↔
          q ∈ Box.Icc L ∧ q ∉ F
        rw [hrect_iff]
        simp only [FL, mem_inter_iff, not_and, hbad_iff]
        tauto
      have htargetMeas : MeasurableSet (rect \ FL) :=
        hrectcompact.isClosed.measurableSet.diff hFLcompact.isClosed.measurableSet
      have hmeasureClosed : volume (Box.Icc L \ F) =
          (volume.prod volume) (rect \ FL) := by
        have hm := (volume_preserving_finTwoArrow ℝ).measure_preimage
          htargetMeas.nullMeasurableSet
        rwa [hpre] at hm
      have hmeasureCoe : volume ((L : Set (Fin 2 → ℝ)) \ F) =
          volume (Box.Icc L \ F) := by
        apply measure_congr
        filter_upwards [Box.coe_ae_eq_Icc (I := L)] with q hq
        simp only [Set.mem_sdiff, hq]
      have hmeasureReal : (volume.prod volume).real (rect \ FL) =
          volume.real ((L : Set (Fin 2 → ℝ)) \ F) := by
        exact congrArg ENNReal.toReal (hmeasureClosed.symm.trans hmeasureCoe.symm)
      change ‖loomanBoundary fe L‖ ≤
        ((4 + 16 * (J.distortion : ℝ)) * (n + 1)) *
          volume.real ((L : Set (Fin 2 → ℝ)) \ F)
      change ‖loomanRectBoundary fe (L.lower 0) (L.upper 0)
        (L.lower 1) (L.upper 1)‖ ≤ _
      rw [← hmeasureReal]
      simpa [rect, mul_assoc] using hestimate)
    exact hg
  have hrectzero : ∀ a b c d, A < a → a < b → b < B₁ →
      C < c → c < d → d < D → loomanRectBoundary fe a b c d = 0 := by
    intro a b c d hAa hab hbB hCc hcd hdD
    let J := loomanRectBox a b c d hab hcd
    have hJI : J ≤ I := by
      rw [Box.le_iff_bounds]
      constructor
      · intro i
        fin_cases i
        · exact hAa.le
        · exact hCc.le
      · intro i
        fin_cases i
        · exact hbB.le
        · exact hdD.le
    have h := hbox J hJI
    simpa [J, looman_rectBox_boundary] using h
  let U : Set ℂ := Ioo A B₁ ×ℂ Ioo C D
  have hUopen : IsOpen U := isOpen_Ioo.reProdIm isOpen_Ioo
  have hfediff : DifferentiableOn ℂ fe U :=
    looman_differentiableOn_Ioo_of_rectBoundary_eq_zero hfecont hrectzero
  have hUs : U ⊆ s := by
    intro z hz
    apply hKs
    rw [Complex.mem_reProdIm] at hz ⊢
    dsimp [A, B₁, C, D] at hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hfdiff : DifferentiableOn ℂ f U := by
    intro z hz
    have hzat : DifferentiableAt ℂ fe z :=
      (hfediff z hz).differentiableAt (hUopen.mem_nhds hz)
    rw [Complex.mem_reProdIm] at hz
    have heq : fe =ᶠ[nhds z] f := hfe_eq_nhds ⟨hz.1.1.le, hz.1.2.le⟩
      ⟨hz.2.1.le, hz.2.2.le⟩
    exact (hzat.congr_of_eventuallyEq heq.symm).differentiableWithinAt
  have hwU : (w : ℂ) ∈ U := by
    rw [Complex.mem_reProdIm]
    dsimp [A, B₁, C, D]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hwH : (w : ℂ) ∈ H := ⟨U, hUopen, hwU, hUs, hfdiff⟩
  exact w.property.2 hwH

end
end MetaMathlibExt
