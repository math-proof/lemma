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
import Def.Analysis.Complex.LoomanMenchoff.Part2
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

theorem looman_rectBoundary_split_x {f : ℂ → ℂ} (hf : Continuous f)
    {A x B C D : ℝ} :
    loomanRectBoundary f A x C D + loomanRectBoundary f x B C D =
      loomanRectBoundary f A B C D := by
  have hh₁ : IntervalIntegrable
      (fun t : ℝ ↦ f (loomanPoint t C) - f (loomanPoint t D)) volume A x :=
    (show Continuous (fun t : ℝ ↦
      f (loomanPoint t C) - f (loomanPoint t D)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hh₂ : IntervalIntegrable
      (fun t : ℝ ↦ f (loomanPoint t C) - f (loomanPoint t D)) volume x B :=
    (show Continuous (fun t : ℝ ↦
      f (loomanPoint t C) - f (loomanPoint t D)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hv₁ : IntervalIntegrable
      (fun y : ℝ ↦ f (loomanPoint x y) - f (loomanPoint A y)) volume C D :=
    (show Continuous (fun y : ℝ ↦
      f (loomanPoint x y) - f (loomanPoint A y)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hv₂ : IntervalIntegrable
      (fun y : ℝ ↦ f (loomanPoint B y) - f (loomanPoint x y)) volume C D :=
    (show Continuous (fun y : ℝ ↦
      f (loomanPoint B y) - f (loomanPoint x y)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  unfold loomanRectBoundary
  calc
    ((∫ t in A..x, f (loomanPoint t C) - f (loomanPoint t D)) +
          Complex.I * ∫ y in C..D, f (loomanPoint x y) - f (loomanPoint A y)) +
        ((∫ t in x..B, f (loomanPoint t C) - f (loomanPoint t D)) +
          Complex.I * ∫ y in C..D, f (loomanPoint B y) - f (loomanPoint x y)) =
        ((∫ t in A..x, f (loomanPoint t C) - f (loomanPoint t D)) +
          ∫ t in x..B, f (loomanPoint t C) - f (loomanPoint t D)) +
          Complex.I * ((∫ y in C..D, f (loomanPoint x y) - f (loomanPoint A y)) +
            ∫ y in C..D, f (loomanPoint B y) - f (loomanPoint x y)) := by ring
    _ = (∫ t in A..B, f (loomanPoint t C) - f (loomanPoint t D)) +
          Complex.I * ((∫ y in C..D, f (loomanPoint x y) - f (loomanPoint A y)) +
            ∫ y in C..D, f (loomanPoint B y) - f (loomanPoint x y)) := by
      rw [intervalIntegral.integral_add_adjacent_intervals hh₁ hh₂]
    _ = _ := by
      rw [← intervalIntegral.integral_add hv₁ hv₂]
      congr 2
      apply intervalIntegral.integral_congr
      intro y _
      ring

theorem looman_rectBoundary_split_y {f : ℂ → ℂ} (hf : Continuous f)
    {A B C y D : ℝ} :
    loomanRectBoundary f A B C y + loomanRectBoundary f A B y D =
      loomanRectBoundary f A B C D := by
  have hh₁ : IntervalIntegrable
      (fun t : ℝ ↦ f (loomanPoint t C) - f (loomanPoint t y)) volume A B :=
    (show Continuous (fun t : ℝ ↦
      f (loomanPoint t C) - f (loomanPoint t y)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hh₂ : IntervalIntegrable
      (fun t : ℝ ↦ f (loomanPoint t y) - f (loomanPoint t D)) volume A B :=
    (show Continuous (fun t : ℝ ↦
      f (loomanPoint t y) - f (loomanPoint t D)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hv₁ : IntervalIntegrable
      (fun t : ℝ ↦ f (loomanPoint B t) - f (loomanPoint A t)) volume C y :=
    (show Continuous (fun t : ℝ ↦
      f (loomanPoint B t) - f (loomanPoint A t)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hv₂ : IntervalIntegrable
      (fun t : ℝ ↦ f (loomanPoint B t) - f (loomanPoint A t)) volume y D :=
    (show Continuous (fun t : ℝ ↦
      f (loomanPoint B t) - f (loomanPoint A t)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  unfold loomanRectBoundary
  calc
    ((∫ t in A..B, f (loomanPoint t C) - f (loomanPoint t y)) +
          Complex.I * ∫ t in C..y, f (loomanPoint B t) - f (loomanPoint A t)) +
        ((∫ t in A..B, f (loomanPoint t y) - f (loomanPoint t D)) +
          Complex.I * ∫ t in y..D, f (loomanPoint B t) - f (loomanPoint A t)) =
        ((∫ t in A..B, f (loomanPoint t C) - f (loomanPoint t y)) +
          ∫ t in A..B, f (loomanPoint t y) - f (loomanPoint t D)) +
          Complex.I * ((∫ t in C..y, f (loomanPoint B t) - f (loomanPoint A t)) +
            ∫ t in y..D, f (loomanPoint B t) - f (loomanPoint A t)) := by ring
    _ = ((∫ t in A..B, f (loomanPoint t C) - f (loomanPoint t y)) +
          ∫ t in A..B, f (loomanPoint t y) - f (loomanPoint t D)) +
          Complex.I * ∫ t in C..D, f (loomanPoint B t) - f (loomanPoint A t) := by
      rw [intervalIntegral.integral_add_adjacent_intervals hv₁ hv₂]
    _ = _ := by
      rw [← intervalIntegral.integral_add hh₁ hh₂]
      congr 2
      funext t
      ring

theorem looman_rectBoundary_eq_zero_of_differentiableOn
    {f : ℂ → ℂ} {A B C D : ℝ} (hAB : A ≤ B) (hCD : C ≤ D)
    (hcont : Continuous f)
    (hdiff : ∀ x ∈ Ioo A B, ∀ y ∈ Ioo C D,
      DifferentiableAt ℂ f (loomanPoint x y)) :
    loomanRectBoundary f A B C D = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f (loomanPoint A C) (loomanPoint B D) hcont.continuousOn (by
      intro z hz
      have hzre : z.re ∈ Ioo A B := by simpa [loomanPoint, hAB] using hz.1
      have hzim : z.im ∈ Ioo C D := by simpa [loomanPoint, hCD] using hz.2
      rw [show z = loomanPoint z.re z.im by
        rw [loomanPoint]
        exact (Complex.re_add_im z).symm]
      exact (hdiff z.re hzre z.im hzim).differentiableWithinAt)
  have hh₁ : IntervalIntegrable (fun x : ℝ ↦ f (loomanPoint x C)) volume A B :=
    (show Continuous (fun x : ℝ ↦ f (loomanPoint x C)) by
      unfold loomanPoint
      fun_prop).intervalIntegrable _ _
  have hh₂ : IntervalIntegrable (fun x : ℝ ↦ f (loomanPoint x D)) volume A B :=
    (show Continuous (fun x : ℝ ↦ f (loomanPoint x D)) by
      unfold loomanPoint
      fun_prop).intervalIntegrable _ _
  have hv₁ : IntervalIntegrable (fun y : ℝ ↦ f (loomanPoint B y)) volume C D :=
    (show Continuous (fun y : ℝ ↦ f (loomanPoint B y)) by
      unfold loomanPoint
      fun_prop).intervalIntegrable _ _
  have hv₂ : IntervalIntegrable (fun y : ℝ ↦ f (loomanPoint A y)) volume C D :=
    (show Continuous (fun y : ℝ ↦ f (loomanPoint A y)) by
      unfold loomanPoint
      fun_prop).intervalIntegrable _ _
  rw [loomanRectBoundary, intervalIntegral.integral_sub hh₁ hh₂,
    intervalIntegral.integral_sub hv₁ hv₂]
  have h' := h
  simp [loomanPoint, smul_eq_mul] at h'
  simp only [loomanPoint]
  linear_combination h'

theorem looman_rectBoundary_eq_hull
    {f : ℂ → ℂ} {F : Set (ℝ × ℝ)} {A B C D a b c d : ℝ}
    (hAa : A ≤ a) (hab : a ≤ b) (hbB : b ≤ B)
    (hCc : C ≤ c) (hcd : c ≤ d) (hdD : d ≤ D)
    (hcont : Continuous f) (hFsub : F ⊆ Icc a b ×ˢ Icc c d)
    (hdiff : ∀ x ∈ Ioo A B, ∀ y ∈ Ioo C D, (x, y) ∉ F →
      DifferentiableAt ℂ f (loomanPoint x y)) :
    loomanRectBoundary f A B C D = loomanRectBoundary f a b c d := by
  have hleft : loomanRectBoundary f A a C D = 0 :=
    looman_rectBoundary_eq_zero_of_differentiableOn hAa
      (hCc.trans <| hcd.trans hdD) hcont <| by
        intro x hx y hy
        exact hdiff x ⟨hx.1, hx.2.trans_le (hab.trans hbB)⟩ y hy fun hF ↦
          (not_le_of_gt hx.2) (hFsub hF).1.1
  have hright : loomanRectBoundary f b B C D = 0 :=
    looman_rectBoundary_eq_zero_of_differentiableOn hbB
      (hCc.trans <| hcd.trans hdD) hcont <| by
        intro x hx y hy
        exact hdiff x ⟨(hAa.trans hab).trans_lt hx.1, hx.2⟩ y hy fun hF ↦
          (not_le_of_gt hx.1) (hFsub hF).1.2
  have hbottom : loomanRectBoundary f a b C c = 0 :=
    looman_rectBoundary_eq_zero_of_differentiableOn hab hCc hcont <| by
      intro x hx y hy
      exact hdiff x ⟨hAa.trans_lt hx.1, hx.2.trans_le hbB⟩ y
        ⟨hy.1, hy.2.trans_le (hcd.trans hdD)⟩ fun hF ↦
          (not_le_of_gt hy.2) (hFsub hF).2.1
  have htop : loomanRectBoundary f a b d D = 0 :=
    looman_rectBoundary_eq_zero_of_differentiableOn hab hdD hcont <| by
      intro x hx y hy
      exact hdiff x ⟨hAa.trans_lt hx.1, hx.2.trans_le hbB⟩ y
        ⟨(hCc.trans hcd).trans_lt hy.1, hy.2⟩ fun hF ↦
          (not_le_of_gt hy.1) (hFsub hF).2.2
  calc
    loomanRectBoundary f A B C D =
        loomanRectBoundary f A a C D + loomanRectBoundary f a B C D :=
      (looman_rectBoundary_split_x hcont).symm
    _ = loomanRectBoundary f a B C D := by rw [hleft, zero_add]
    _ = loomanRectBoundary f a b C D + loomanRectBoundary f b B C D :=
      (looman_rectBoundary_split_x hcont).symm
    _ = loomanRectBoundary f a b C D := by rw [hright, add_zero]
    _ = loomanRectBoundary f a b C c + loomanRectBoundary f a b c D :=
      (looman_rectBoundary_split_y hcont).symm
    _ = loomanRectBoundary f a b c D := by rw [hbottom, zero_add]
    _ = loomanRectBoundary f a b c d + loomanRectBoundary f a b d D :=
      (looman_rectBoundary_split_y hcont).symm
    _ = loomanRectBoundary f a b c d := by rw [htop, add_zero]

theorem looman_rectBoundary_re_eq {f : ℂ → ℂ} (hf : Continuous f)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (loomanRectBoundary f a b c d).re =
      -(∫ x in Icc a b, (f (loomanPoint x d)).re - (f (loomanPoint x c)).re) -
        ∫ y in Icc c d, (f (loomanPoint b y)).im - (f (loomanPoint a y)).im := by
  have hh : IntervalIntegrable
      (fun x : ℝ ↦ f (loomanPoint x c) - f (loomanPoint x d)) volume a b :=
    (show Continuous (fun x : ℝ ↦
      f (loomanPoint x c) - f (loomanPoint x d)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hv : IntervalIntegrable
      (fun y : ℝ ↦ f (loomanPoint b y) - f (loomanPoint a y)) volume c d :=
    (show Continuous (fun y : ℝ ↦
      f (loomanPoint b y) - f (loomanPoint a y)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hh_re : (∫ x in a..b,
      f (loomanPoint x c) - f (loomanPoint x d)).re =
      ∫ x in a..b, (f (loomanPoint x c) - f (loomanPoint x d)).re := by
    symm
    simpa using intervalIntegral.intervalIntegral_re hh
  have hv_im : (∫ y in c..d,
      f (loomanPoint b y) - f (loomanPoint a y)).im =
      ∫ y in c..d, (f (loomanPoint b y) - f (loomanPoint a y)).im := by
    symm
    simpa using intervalIntegral.intervalIntegral_im hv
  rw [loomanRectBoundary]
  rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, hh_re, hv_im]
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  apply congrArg₂ Sub.sub
  · rw [← MeasureTheory.integral_neg]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    simp
  · rfl

theorem looman_rectBoundary_im_eq {f : ℂ → ℂ} (hf : Continuous f)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (loomanRectBoundary f a b c d).im =
      -(∫ x in Icc a b, (f (loomanPoint x d)).im - (f (loomanPoint x c)).im) +
        ∫ y in Icc c d, (f (loomanPoint b y)).re - (f (loomanPoint a y)).re := by
  have hh : IntervalIntegrable
      (fun x : ℝ ↦ f (loomanPoint x c) - f (loomanPoint x d)) volume a b :=
    (show Continuous (fun x : ℝ ↦
      f (loomanPoint x c) - f (loomanPoint x d)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hv : IntervalIntegrable
      (fun y : ℝ ↦ f (loomanPoint b y) - f (loomanPoint a y)) volume c d :=
    (show Continuous (fun y : ℝ ↦
      f (loomanPoint b y) - f (loomanPoint a y)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hh_im : (∫ x in a..b,
      f (loomanPoint x c) - f (loomanPoint x d)).im =
      ∫ x in a..b, (f (loomanPoint x c) - f (loomanPoint x d)).im := by
    symm
    simpa using intervalIntegral.intervalIntegral_im hh
  have hv_re : (∫ y in c..d,
      f (loomanPoint b y) - f (loomanPoint a y)).re =
      ∫ y in c..d, (f (loomanPoint b y) - f (loomanPoint a y)).re := by
    symm
    simpa using intervalIntegral.intervalIntegral_re hv
  rw [loomanRectBoundary]
  rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_add, hh_im, hv_re]
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  apply congrArg₂ Add.add
  · rw [← MeasureTheory.integral_neg]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    simp
  · rfl

theorem looman_exists_coordinate_hull {F : Set (ℝ × ℝ)} {A B C D : ℝ}
    (hFcompact : IsCompact F) (hFne : F.Nonempty)
    (hFsub : F ⊆ Icc A B ×ˢ Icc C D) :
    ∃ a b c d,
      A ≤ a ∧ a ≤ b ∧ b ≤ B ∧ C ≤ c ∧ c ≤ d ∧ d ≤ D ∧
      F ⊆ Icc a b ×ˢ Icc c d ∧
      (∃ y, (a, y) ∈ F) ∧ (∃ y, (b, y) ∈ F) ∧
      (∃ x, (x, c) ∈ F) ∧ (∃ x, (x, d) ∈ F) := by
  obtain ⟨pa, hpaF, hpa⟩ :=
    hFcompact.exists_isMinOn hFne continuous_fst.continuousOn
  obtain ⟨pb, hpbF, hpb⟩ :=
    hFcompact.exists_isMaxOn hFne continuous_fst.continuousOn
  obtain ⟨pc, hpcF, hpc⟩ :=
    hFcompact.exists_isMinOn hFne continuous_snd.continuousOn
  obtain ⟨pd, hpdF, hpd⟩ :=
    hFcompact.exists_isMaxOn hFne continuous_snd.continuousOn
  refine ⟨pa.1, pb.1, pc.2, pd.2, (hFsub hpaF).1.1, hpa hpbF,
    (hFsub hpbF).1.2, (hFsub hpcF).2.1, hpc hpdF, (hFsub hpdF).2.2, ?_,
    ⟨pa.2, hpaF⟩, ⟨pb.2, hpbF⟩, ⟨pc.1, hpcF⟩, ⟨pd.1, hpdF⟩⟩
  intro p hp
  exact ⟨⟨hpa hp, hpb hp⟩, hpc hp, hpd hp⟩

theorem looman_rectBoundary_norm_le
    {f : ℂ → ℂ} {F : Set (ℝ × ℝ)}
    {A B C D K L κ : ℝ} {ux uy vx vy : ℝ × ℝ → ℝ}
    (hAB : A < B) (hCD : C < D) (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hLx : B - A ≤ L) (hLy : D - C ≤ L)
    (hLheight : L ≤ κ * (D - C)) (hLwidth : L ≤ κ * (B - A))
    (hcont : Continuous f) (hFcompact : IsCompact F) (hFne : F.Nonempty)
    (hFsub : F ⊆ Icc A B ×ˢ Icc C D)
    (hhol : ∀ x ∈ Ioo A B, ∀ y ∈ Ioo C D, (x, y) ∉ F →
      DifferentiableAt ℂ f (loomanPoint x y))
    (hux : ∀ p ∈ F,
      HasDerivAt (fun x ↦ (f (loomanPoint x p.2)).re) (ux p) p.1)
    (huy : ∀ p ∈ F,
      HasDerivAt (fun y ↦ (f (loomanPoint p.1 y)).re) (uy p) p.2)
    (hvx : ∀ p ∈ F,
      HasDerivAt (fun x ↦ (f (loomanPoint x p.2)).im) (vx p) p.1)
    (hvy : ∀ p ∈ F,
      HasDerivAt (fun y ↦ (f (loomanPoint p.1 y)).im) (vy p) p.2)
    (huxK : ∀ p ∈ F, |ux p| ≤ K) (huyK : ∀ p ∈ F, |uy p| ≤ K)
    (hvxK : ∀ p ∈ F, |vx p| ≤ K) (hvyK : ∀ p ∈ F, |vy p| ≤ K)
    (hcr₁ : ∀ p ∈ F, ux p = vy p) (hcr₂ : ∀ p ∈ F, uy p = -(vx p))
    (hLipX : ∀ p ∈ F, ∀ x ∈ Icc A B,
      ‖f (loomanPoint x p.2) - f (loomanPoint p.1 p.2)‖ ≤ K * |x - p.1|)
    (hLipY : ∀ p ∈ F, ∀ y ∈ Icc C D,
      ‖f (loomanPoint p.1 y) - f (loomanPoint p.1 p.2)‖ ≤ K * |y - p.2|) :
    ‖loomanRectBoundary f A B C D‖ ≤
      (4 + 16 * κ) * K * (volume.prod volume).real
        ((Icc A B ×ˢ Icc C D) \ F) := by
  obtain ⟨a, b, c, d, hAa, hab, hbB, hCc, hcd, hdD, hFhull,
    hleft, hright, hbot, htop⟩ :=
    looman_exists_coordinate_hull hFcompact hFne hFsub
  let u : ℝ × ℝ → ℝ := fun p ↦ (f (loomanPoint p.1 p.2)).re
  let v : ℝ × ℝ → ℝ := fun p ↦ (f (loomanPoint p.1 p.2)).im
  have hucont : Continuous u := by unfold u loomanPoint; fun_prop
  have hvcont : Continuous v := by unfold v loomanPoint; fun_prop
  have huLipX : ∀ p ∈ F, ∀ x ∈ Icc A B,
      |u (x, p.2) - u p| ≤ K * |x - p.1| := by
    intro p hp x hx
    calc
      |u (x, p.2) - u p| =
          |(f (loomanPoint x p.2) - f (loomanPoint p.1 p.2)).re| := by rfl
      _ ≤ ‖f (loomanPoint x p.2) - f (loomanPoint p.1 p.2)‖ :=
        Complex.abs_re_le_norm _
      _ ≤ K * |x - p.1| := hLipX p hp x hx
  have huLipY : ∀ p ∈ F, ∀ y ∈ Icc C D,
      |u (p.1, y) - u p| ≤ K * |y - p.2| := by
    intro p hp y hy
    calc
      |u (p.1, y) - u p| =
          |(f (loomanPoint p.1 y) - f (loomanPoint p.1 p.2)).re| := by rfl
      _ ≤ ‖f (loomanPoint p.1 y) - f (loomanPoint p.1 p.2)‖ :=
        Complex.abs_re_le_norm _
      _ ≤ K * |y - p.2| := hLipY p hp y hy
  have hvLipX : ∀ p ∈ F, ∀ x ∈ Icc A B,
      |v (x, p.2) - v p| ≤ K * |x - p.1| := by
    intro p hp x hx
    calc
      |v (x, p.2) - v p| =
          |(f (loomanPoint x p.2) - f (loomanPoint p.1 p.2)).im| := by rfl
      _ ≤ ‖f (loomanPoint x p.2) - f (loomanPoint p.1 p.2)‖ :=
        Complex.abs_im_le_norm _
      _ ≤ K * |x - p.1| := hLipX p hp x hx
  have hvLipY : ∀ p ∈ F, ∀ y ∈ Icc C D,
      |v (p.1, y) - v p| ≤ K * |y - p.2| := by
    intro p hp y hy
    calc
      |v (p.1, y) - v p| =
          |(f (loomanPoint p.1 y) - f (loomanPoint p.1 p.2)).im| := by rfl
      _ ≤ ‖f (loomanPoint p.1 y) - f (loomanPoint p.1 p.2)‖ :=
        Complex.abs_im_le_norm _
      _ ≤ K * |y - p.2| := hLipY p hp y hy
  let m := (1 + 4 * κ) * K * (volume.prod volume).real
    ((Icc A B ×ˢ Icc C D) \ F)
  have huY := looman_vertical_estimate hAa hbB hCc hcd hdD hCD hK hκ
    hLx hLy hLheight hucont hFcompact.isClosed hFcompact hFhull hbot htop
    (fun p hp ↦ (huy p hp).differentiableAt)
    (fun p hp ↦ by rw [(huy p hp).deriv]; exact huyK p hp) huLipX huLipY
  have hvY := looman_vertical_estimate hAa hbB hCc hcd hdD hCD hK hκ
    hLx hLy hLheight hvcont hFcompact.isClosed hFcompact hFhull hbot htop
    (fun p hp ↦ (hvy p hp).differentiableAt)
    (fun p hp ↦ by rw [(hvy p hp).deriv]; exact hvyK p hp) hvLipX hvLipY
  have huX := looman_horizontal_estimate hAa hab hbB hCc hdD hAB hK hκ
    hLx hLy hLwidth hucont hFcompact.isClosed hFcompact hFhull hleft hright
    (fun p hp ↦ (hux p hp).differentiableAt)
    (fun p hp ↦ by rw [(hux p hp).deriv]; exact huxK p hp) huLipX huLipY
  have hvX := looman_horizontal_estimate hAa hab hbB hCc hdD hAB hK hκ
    hLx hLy hLwidth hvcont hFcompact.isClosed hFcompact hFhull hleft hright
    (fun p hp ↦ (hvx p hp).differentiableAt)
    (fun p hp ↦ by rw [(hvx p hp).deriv]; exact hvxK p hp) hvLipX hvLipY
  let UY := ∫ p in F, deriv (fun y ↦ u (p.1, y)) p.2 ∂(volume.prod volume)
  let VY := ∫ p in F, deriv (fun y ↦ v (p.1, y)) p.2 ∂(volume.prod volume)
  let UX := ∫ p in F, deriv (fun x ↦ u (x, p.2)) p.1 ∂(volume.prod volume)
  let VX := ∫ p in F, deriv (fun x ↦ v (x, p.2)) p.1 ∂(volume.prod volume)
  have hcrY : UY = -VX := by
    rw [← MeasureTheory.integral_neg]
    apply setIntegral_congr_fun hFcompact.isClosed.measurableSet
    intro p hp
    change deriv (fun y ↦ (f (loomanPoint p.1 y)).re) p.2 =
      -deriv (fun x ↦ (f (loomanPoint x p.2)).im) p.1
    rw [(huy p hp).deriv, (hvx p hp).deriv, hcr₂ p hp]
  have hcrX : UX = VY := by
    apply setIntegral_congr_fun hFcompact.isClosed.measurableSet
    intro p hp
    change deriv (fun x ↦ (f (loomanPoint x p.2)).re) p.1 =
      deriv (fun y ↦ (f (loomanPoint p.1 y)).im) p.2
    rw [(hux p hp).deriv, (hvy p hp).deriv, hcr₁ p hp]
  let Vu := ∫ x in Icc a b, u (x, d) - u (x, c)
  let Vv := ∫ x in Icc a b, v (x, d) - v (x, c)
  let Hu := ∫ y in Icc c d, u (b, y) - u (a, y)
  let Hv := ∫ y in Icc c d, v (b, y) - v (a, y)
  have huY' : |Vu - UY| ≤ m := by simpa [Vu, UY, m] using huY
  have hvY' : |Vv - VY| ≤ m := by simpa [Vv, VY, m] using hvY
  have huX' : |Hu - UX| ≤ m := by simpa [Hu, UX, m] using huX
  have hvX' : |Hv - VX| ≤ m := by simpa [Hv, VX, m] using hvX
  have hre : |-Vu - Hv| ≤ m + m := by
    rw [show -Vu - Hv = -(Vu - UY) - (Hv - VX) by rw [hcrY]; ring]
    calc
      |-(Vu - UY) - (Hv - VX)| = |(Vu - UY) + (Hv - VX)| := by
        rw [show -(Vu - UY) - (Hv - VX) = -((Vu - UY) + (Hv - VX)) by ring,
          abs_neg]
      _ ≤ |Vu - UY| + |Hv - VX| := abs_add_le _ _
      _ ≤ m + m := add_le_add huY' hvX'
  have him : |-Vv + Hu| ≤ m + m := by
    rw [show -Vv + Hu = -(Vv - VY) + (Hu - UX) by rw [hcrX]; ring]
    calc
      |-(Vv - VY) + (Hu - UX)| ≤ |-(Vv - VY)| + |Hu - UX| := abs_add_le _ _
      _ = |Vv - VY| + |Hu - UX| := by rw [abs_neg]
      _ ≤ m + m := add_le_add hvY' huX'
  have hhull := looman_rectBoundary_eq_hull hAa hab hbB hCc hcd hdD
    hcont hFhull hhol
  rw [hhull]
  calc
    ‖loomanRectBoundary f a b c d‖ ≤
        |(loomanRectBoundary f a b c d).re| +
          |(loomanRectBoundary f a b c d).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |-Vu - Hv| + |-Vv + Hu| := by
      rw [looman_rectBoundary_re_eq hcont hab hcd,
        looman_rectBoundary_im_eq hcont hab hcd]
    _ ≤ (m + m) + (m + m) := add_le_add hre him
    _ = (4 + 16 * κ) * K * (volume.prod volume).real
        ((Icc A B ×ˢ Icc C D) \ F) := by
      dsimp [m]
      ring

end
end MetaMathlibExt
