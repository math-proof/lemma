/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.TietzeExtension
import Def.Analysis.Complex.HartogsSeparateAnalyticity
/-!
# Hartogs' theorem on separate analyticity

This file proves that a scalar-valued function on finite-dimensional complex Euclidean space is
holomorphic when it is holomorphic in each coordinate separately.
-/


namespace Complex.HartogsWanted

open Set Metric Filter ContinuousLinearMap

open MeasureTheory

open scoped Topology

@[simp]
lemma hartogsPolydiscIntegral_zero
    (u : (Fin 0 → ℂ) → ℝ) (c : Fin 0 → ℂ) (R : ℝ) :
    hartogsPolydiscIntegral u c R = u c := rfl

lemma hartogsPolydiscIntegral_succ {n : ℕ}
    (u : (Fin (n + 1) → ℂ) → ℝ) (c : Fin (n + 1) → ℂ) (R : ℝ) :
    hartogsPolydiscIntegral u c R =
      ∫ z in closedBall (c 0) R,
        hartogsPolydiscIntegral (fun y ↦ u (Fin.cons z y)) (c ∘ Fin.succ) R := rfl

lemma hartogsPolydiscIntegral_succ_add {n : ℕ}
    (u : (Fin (n + 1) → ℂ) → ℝ) (c : Fin (n + 1) → ℂ) (R : ℝ) :
    hartogsPolydiscIntegral u c R =
      ∫ t in closedBall (0 : ℂ) R,
        hartogsPolydiscIntegral (fun y ↦ u (Fin.cons (t + c 0) y))
          (c ∘ Fin.succ) R := by
  rw [hartogsPolydiscIntegral_succ]
  exact (diskIntegral_add_center
    (fun z ↦ hartogsPolydiscIntegral (fun y ↦ u (Fin.cons z y))
      (c ∘ Fin.succ) R) (c 0) R).symm

theorem continuous_hartogsPolydiscIntegral_param
    {n : ℕ} {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [LocallyCompactSpace X] {u : X → (Fin n → ℂ) → ℝ}
    (hu : Continuous (Function.uncurry u))
    {c : X → Fin n → ℂ} (hc : Continuous c) (R : ℝ) :
    Continuous (fun x ↦ hartogsPolydiscIntegral (u x) (c x) R) := by
  induction n generalizing X with
  | zero =>
      change Continuous (fun x ↦ u x (c x))
      exact hu.comp (continuous_id.prodMk hc)
  | succ n ih =>
      simp_rw [hartogsPolydiscIntegral_succ_add]
      apply continuous_parametric_integral_of_continuous
      · change Continuous (Function.uncurry fun x t ↦
          hartogsPolydiscIntegral
            (fun y ↦ u x (Fin.cons (t + c x 0) y)) (c x ∘ Fin.succ) R)
        apply ih
        · change Continuous (fun p : (X × ℂ) × (Fin n → ℂ) ↦
            u p.1.1 (Fin.cons (p.1.2 + c p.1.1 0) p.2))
          have hvec : Continuous (fun p : (X × ℂ) × (Fin n → ℂ) ↦
              (Fin.cons (p.1.2 + c p.1.1 0) p.2 : Fin (n + 1) → ℂ)) := by
            apply continuous_pi
            intro i
            refine Fin.cases ?_ (fun j ↦ ?_) i
            · simp only [Fin.cons_zero]
              fun_prop
            · simp only [Fin.cons_succ]
              fun_prop
          exact hu.comp ((continuous_fst.comp continuous_fst).prodMk hvec)
        · change Continuous (fun p : X × ℂ ↦ c p.1 ∘ Fin.succ)
          fun_prop
      · exact isCompact_closedBall (0 : ℂ) R

/-- Iterating the circle sub-mean inequality gives the corresponding inequality for the
solid polydisc average. -/
theorem hartogsPolydisc_submean
    {n : ℕ} {u : (Fin n → ℂ) → ℝ} (hu : Continuous u)
    {c : Fin n → ℂ} {R : ℝ} (hR : 0 < R)
    (hcircle : ∀ x ∈ closedBall c R, ∀ (i : Fin n) r, r ∈ Ioc 0 R →
      u x ≤ Real.circleAverage (fun z ↦ u (Function.update x i z)) (x i) r) :
    (volume (closedBall (0 : ℂ) R)).toReal ^ n * u c ≤
      hartogsPolydiscIntegral u c R := by
  induction n with
  | zero => simp
  | succ n ih =>
      let c' : Fin n → ℂ := c ∘ Fin.succ
      let A : ℝ := (volume (closedBall (0 : ℂ) R)).toReal ^ n
      let g : ℂ → ℝ := fun z ↦ A * u (Fin.cons z c')
      have hA : 0 ≤ A := pow_nonneg ENNReal.toReal_nonneg _
      have hg : Continuous g := by
        apply continuous_const.mul
        apply hu.comp
        apply continuous_pi
        intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simp only [Fin.cons_zero]
          change Continuous (id : ℂ → ℂ)
          exact continuous_id
        · simp only [Fin.cons_succ]
          exact continuous_const
      have hgsub : ∀ r ∈ Ioc 0 R,
          g (c 0) ≤ Real.circleAverage g (c 0) r := by
        intro r hr
        have hc_cons : Fin.cons (c 0) c' = c := by
          funext i
          refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [c']
        have hslice : (fun z ↦ u (Function.update c 0 z)) =
            fun z ↦ u (Fin.cons z c') := by
          funext z
          congr 1
          funext i
          refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [c']
        have h := hcircle c (by simp [hR.le]) 0 r hr
        rw [hslice] at h
        dsimp [g]
        rw [hc_cons]
        rw [show (fun z ↦ A * u (Fin.cons z c')) =
          A • (fun z ↦ u (Fin.cons z c')) by rfl]
        rw [Real.circleAverage_smul]
        exact mul_le_mul_of_nonneg_left h hA
      have hdisc := disk_submean hg hR hgsub
      have hmono :
          (∫ z in closedBall (c 0) R, g z) ≤
            ∫ z in closedBall (c 0) R,
              hartogsPolydiscIntegral (fun y ↦ u (Fin.cons z y)) c' R := by
        apply MeasureTheory.setIntegral_mono_on
        · exact hg.continuousOn.integrableOn_compact
            (isCompact_closedBall _ _)
        · have hp : Continuous (fun z ↦
              hartogsPolydiscIntegral (fun y ↦ u (Fin.cons z y)) c' R) := by
            apply continuous_hartogsPolydiscIntegral_param
            · change Continuous (fun p : ℂ × (Fin n → ℂ) ↦
                u (Fin.cons p.1 p.2))
              apply hu.comp
              apply continuous_pi
              intro i
              refine Fin.cases ?_ (fun j ↦ ?_) i
              · simp only [Fin.cons_zero]
                change Continuous (Prod.fst : ℂ × (Fin n → ℂ) → ℂ)
                exact continuous_fst
              · simp only [Fin.cons_succ]
                change Continuous ((fun y : Fin n → ℂ ↦ y j) ∘ Prod.snd)
                exact (continuous_apply j).comp continuous_snd
            · exact continuous_const
          exact hp.continuousOn.integrableOn_compact
            (isCompact_closedBall _ _)
        · exact measurableSet_closedBall
        · intro z hz
          change A * u (Fin.cons z c') ≤
            hartogsPolydiscIntegral (fun y ↦ u (Fin.cons z y)) c' R
          dsimp [A]
          apply ih (u := fun y ↦ u (Fin.cons z y)) (c := c')
          · change Continuous (fun y ↦ u (Fin.cons z y))
            apply hu.comp
            fun_prop
          · intro y hy i r hr
            have hc_cons' : Fin.cons (c 0) c' = c := by
              funext j
              refine Fin.cases ?_ (fun k ↦ ?_) j <;> simp [c']
            have hxy : Fin.cons z y ∈ closedBall c R := by
              rw [← hc_cons']
              rw [Metric.mem_closedBall, dist_pi_le_iff hR.le]
              intro j
              refine Fin.cases ?_ (fun k ↦ ?_) j
              · simpa [Metric.mem_closedBall] using hz
              · have hy' :=
                  (dist_pi_le_iff hR.le).1
                    (Metric.mem_closedBall.1 hy) k
                simpa using hy'
            have h := hcircle (Fin.cons z y) hxy i.succ r hr
            simpa only [Fin.cons_succ, Fin.cons_update] using h
      rw [hartogsPolydiscIntegral_succ]
      have hc_cons : Fin.cons (c 0) (c ∘ Fin.succ) = c := by
        funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
      have hlhs :
          (volume (closedBall (0 : ℂ) R)).toReal ^ (n + 1) * u c =
            (volume (closedBall (c 0) R)).toReal * g (c 0) := by
        dsimp [g, A, c']
        rw [hc_cons]
        simp only [Complex.volume_closedBall]
        ring
      rw [hlhs]
      exact hdisc.trans hmono

lemma fin_cons_mem_closedBall {n : ℕ} {z c₀ : ℂ}
    {y c' : Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hz : z ∈ closedBall c₀ R) (hy : y ∈ closedBall c' R) :
    (Fin.cons z y : Fin (n + 1) → ℂ) ∈
      closedBall (Fin.cons c₀ c' : Fin (n + 1) → ℂ) R := by
  have hy' : ∀ j, dist (y j) (c' j) ≤ R :=
    (dist_pi_le_iff hR).1 (Metric.mem_closedBall.1 hy)
  rw [Metric.mem_closedBall, dist_pi_le_iff hR]
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa [Metric.mem_closedBall] using hz
  · simpa using hy' j

theorem hartogsPolydiscIntegral_nonneg
    {n : ℕ} {u : (Fin n → ℂ) → ℝ} (hu : ∀ x, 0 ≤ u x)
    (c : Fin n → ℂ) (R : ℝ) :
    0 ≤ hartogsPolydiscIntegral u c R := by
  induction n with
  | zero => exact hu _
  | succ n ih =>
      rw [hartogsPolydiscIntegral_succ]
      exact MeasureTheory.integral_nonneg fun z ↦
        ih (u := fun y ↦ u (Fin.cons z y)) (fun y ↦ hu _)
          (c ∘ Fin.succ)

theorem hartogsPolydiscIntegral_le
    {n : ℕ} {u : (Fin n → ℂ) → ℝ} (hu : Continuous u)
    {c : Fin n → ℂ} {R C : ℝ} (hR : 0 ≤ R)
    (hC : ∀ x ∈ closedBall c R, u x ≤ C) :
    hartogsPolydiscIntegral u c R ≤
      (volume (closedBall (0 : ℂ) R)).toReal ^ n * C := by
  induction n with
  | zero =>
      simpa using hC c (by simp [hR])
  | succ n ih =>
      let c' : Fin n → ℂ := c ∘ Fin.succ
      have hc_cons : Fin.cons (c 0) c' = c := by
        funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [c']
      rw [hartogsPolydiscIntegral_succ]
      calc
        _ ≤ ∫ _z in closedBall (c 0) R,
              (volume (closedBall (0 : ℂ) R)).toReal ^ n * C := by
          apply MeasureTheory.setIntegral_mono_on
          · have hp : Continuous (fun z ↦
                hartogsPolydiscIntegral (fun y ↦ u (Fin.cons z y)) c' R) := by
              apply continuous_hartogsPolydiscIntegral_param
              · change Continuous (fun p : ℂ × (Fin n → ℂ) ↦
                  u (Fin.cons p.1 p.2))
                apply hu.comp
                fun_prop
              · exact continuous_const
            exact hp.continuousOn.integrableOn_compact
              (isCompact_closedBall _ _)
          · exact integrableOn_const measure_closedBall_lt_top.ne
          · exact measurableSet_closedBall
          · intro z hz
            apply ih
            · change Continuous (fun y ↦ u (Fin.cons z y))
              apply hu.comp
              fun_prop
            · intro y hy
              apply hC
              rw [← hc_cons]
              exact fin_cons_mem_closedBall hR hz hy
        _ = (volume (closedBall (0 : ℂ) R)).toReal ^ (n + 1) * C := by
          rw [MeasureTheory.setIntegral_const]
          simp only [smul_eq_mul, measureReal_def, Complex.volume_closedBall]
          ring

theorem tendsto_hartogsPolydiscIntegral_zero
    {n : ℕ} {u : ℕ → (Fin n → ℂ) → ℝ}
    (hu : ∀ k, Continuous (u k))
    (hnonneg : ∀ k x, 0 ≤ u k x) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ k x, u k x ≤ C) {c : Fin n → ℂ} {R : ℝ}
    (hR : 0 ≤ R)
    (hlim : ∀ x ∈ closedBall c R,
      Tendsto (fun k ↦ u k x) atTop (nhds 0)) :
    Tendsto (fun k ↦ hartogsPolydiscIntegral (u k) c R)
      atTop (nhds 0) := by
  induction n with
  | zero =>
      simpa using hlim c (by simp [hR])
  | succ n ih =>
      let c' : Fin n → ℂ := c ∘ Fin.succ
      let B : ℝ := (volume (closedBall (0 : ℂ) R)).toReal ^ n * C
      let F : ℕ → ℂ → ℝ := fun k z ↦
        hartogsPolydiscIntegral (fun y ↦ u k (Fin.cons z y)) c' R
      have hFcont : ∀ k, Continuous (F k) := by
        intro k
        dsimp [F]
        apply continuous_hartogsPolydiscIntegral_param
        · change Continuous (fun p : ℂ × (Fin n → ℂ) ↦
            u k (Fin.cons p.1 p.2))
          apply (hu k).comp
          fun_prop
        · exact continuous_const
      have hB : 0 ≤ B :=
        mul_nonneg (pow_nonneg ENNReal.toReal_nonneg _) hC
      have hFB : ∀ k z, F k z ≤ B := by
        intro k z
        dsimp [F, B]
        apply hartogsPolydiscIntegral_le
        · change Continuous (fun y ↦ u k (Fin.cons z y))
          apply (hu k).comp
          fun_prop
        · exact hR
        · intro y _hy
          exact hbound k _
      have hF0 : ∀ k z, 0 ≤ F k z := by
        intro k z
        exact hartogsPolydiscIntegral_nonneg
          (u := fun y ↦ u k (Fin.cons z y)) (fun y ↦ hnonneg k _)
            c' R
      have hFtendsto : ∀ z ∈ closedBall (c 0) R,
          Tendsto (fun k ↦ F k z) atTop (nhds 0) := by
        intro z hz
        apply ih
        · intro k
          change Continuous (fun y ↦ u k (Fin.cons z y))
          apply (hu k).comp
          fun_prop
        · intro k y
          exact hnonneg k _
        · intro k y
          exact hbound k _
        · intro y hy
          apply hlim
          have hc_cons : Fin.cons (c 0) c' = c := by
            funext i
            refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [c']
          rw [← hc_cons]
          exact fin_cons_mem_closedBall hR hz hy
      have ht := MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := volume.restrict (closedBall (c 0) R)) (fun _ : ℂ ↦ B)
        (fun k ↦ (hFcont k).aestronglyMeasurable)
        (integrableOn_const measure_closedBall_lt_top.ne)
        (fun k ↦ Filter.Eventually.of_forall fun z ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (hF0 k z)]
          exact hFB k z)
        (ae_restrict_of_forall_mem measurableSet_closedBall
          fun z hz ↦ hFtendsto z hz)
      simpa [F, hartogsPolydiscIntegral_succ] using ht

theorem hartogsPolydiscIntegral_mono_center
    {n : ℕ} {u : (Fin n → ℂ) → ℝ} (hu : Continuous u)
    (hu0 : ∀ x, 0 ≤ u x) {c c' : Fin n → ℂ} {R S : ℝ}
    (hsub : ∀ i, closedBall (c' i) S ⊆ closedBall (c i) R) :
    hartogsPolydiscIntegral u c' S ≤ hartogsPolydiscIntegral u c R := by
  induction n with
  | zero =>
      change u c' ≤ u c
      rw [Subsingleton.elim c' c]
  | succ n ih =>
      let d : Fin n → ℂ := c ∘ Fin.succ
      let d' : Fin n → ℂ := c' ∘ Fin.succ
      rw [hartogsPolydiscIntegral_succ, hartogsPolydiscIntegral_succ]
      let F : ℂ → ℝ := fun z ↦
        hartogsPolydiscIntegral (fun y ↦ u (Fin.cons z y)) d R
      let F' : ℂ → ℝ := fun z ↦
        hartogsPolydiscIntegral (fun y ↦ u (Fin.cons z y)) d' S
      have hF : Continuous F := by
        dsimp [F]
        apply continuous_hartogsPolydiscIntegral_param
        · change Continuous (fun p : ℂ × (Fin n → ℂ) ↦
            u (Fin.cons p.1 p.2))
          apply hu.comp
          fun_prop
        · exact continuous_const
      have hF' : Continuous F' := by
        dsimp [F']
        apply continuous_hartogsPolydiscIntegral_param
        · change Continuous (fun p : ℂ × (Fin n → ℂ) ↦
            u (Fin.cons p.1 p.2))
          apply hu.comp
          fun_prop
        · exact continuous_const
      calc
        (∫ z in closedBall (c' 0) S, F' z) ≤
            ∫ z in closedBall (c' 0) S, F z := by
          apply MeasureTheory.setIntegral_mono_on
          · exact hF'.continuousOn.integrableOn_compact
              (isCompact_closedBall _ _)
          · exact hF.continuousOn.integrableOn_compact
              (isCompact_closedBall _ _)
          · exact measurableSet_closedBall
          · intro z _hz
            apply ih
            · change Continuous (fun y ↦ u (Fin.cons z y))
              apply hu.comp
              fun_prop
            · intro y
              exact hu0 _
            · intro i
              exact hsub i.succ
        _ ≤ ∫ z in closedBall (c 0) R, F z := by
          apply MeasureTheory.setIntegral_mono_set
          · exact hF.continuousOn.integrableOn_compact
              (isCompact_closedBall _ _)
          · exact Filter.Eventually.of_forall fun z ↦
              hartogsPolydiscIntegral_nonneg
                (u := fun y ↦ u (Fin.cons z y)) (fun y ↦ hu0 _) d R
          · exact Filter.Eventually.of_forall fun z hz ↦ hsub 0 hz

theorem hartogs_eventually_uniform_of_submean_global
    {n : ℕ} {u : ℕ → (Fin n → ℂ) → ℝ}
    {c : Fin n → ℂ} {R C : ℝ}
    (hR : 0 < R) (hu : ∀ k, Continuous (u k))
    (hu0 : ∀ k x, 0 ≤ u k x) (hC : 0 ≤ C)
    (hub : ∀ k x, u k x ≤ C)
    (hlim : ∀ x ∈ closedBall c R,
      Tendsto (fun k ↦ u k x) atTop (nhds 0))
    (hcircle : ∀ k x (i : Fin n) r, 0 < r →
      (∀ z ∈ closedBall (x i) r,
        Function.update x i z ∈ closedBall c R) →
      u k x ≤
        Real.circleAverage (fun z ↦ u k (Function.update x i z)) (x i) r)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ closedBall c (R / 4), u k x ≤ ε := by
  let S : ℝ := R / 4
  let V : ℝ := (volume (closedBall (0 : ℂ) S)).toReal ^ n
  have hS : 0 < S := div_pos hR (by norm_num)
  have hvol : 0 < (volume (closedBall (0 : ℂ) S)).toReal := by
    rw [Complex.volume_closedBall]
    simpa [ENNReal.toReal_mul, hS.le] using
      mul_pos (pow_pos hS 2) Real.pi_pos
  have hV : 0 < V := pow_pos hvol _
  have ht : Tendsto
      (fun k ↦ hartogsPolydiscIntegral (u k) c R) atTop (nhds 0) :=
    tendsto_hartogsPolydiscIntegral_zero hu hu0 hC hub hR.le hlim
  have hevent : ∀ᶠ k in atTop,
      hartogsPolydiscIntegral (u k) c R < V * ε :=
    (tendsto_order.1 ht).2 _ (mul_pos hV hε)
  filter_upwards [hevent] with k hk
  intro x hx
  have hsubsets : ∀ i,
      closedBall (x i) S ⊆ closedBall (c i) R := by
    intro i z hz
    rw [Metric.mem_closedBall] at hx hz ⊢
    have hxi : dist (x i) (c i) ≤ S :=
      (dist_pi_le_iff hS.le).1 hx i
    calc
      dist z (c i) ≤ dist z (x i) + dist (x i) (c i) :=
        dist_triangle _ _ _
      _ ≤ S + S := add_le_add hz hxi
      _ ≤ R := by dsimp [S]; linarith
  have hmean : V * u k x ≤ hartogsPolydiscIntegral (u k) x S := by
    dsimp [V]
    apply hartogsPolydisc_submean (hu k) hS
    intro y hy i r hr
    apply hcircle k y i r hr.1
    intro z hz
    rw [Metric.mem_closedBall, dist_pi_le_iff hR.le]
    intro j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      have hyi : dist (y i) (x i) ≤ S :=
        (dist_pi_le_iff hS.le).1 (Metric.mem_closedBall.1 hy) i
      have hxi : dist (x i) (c i) ≤ S :=
        (dist_pi_le_iff hS.le).1 (Metric.mem_closedBall.1 hx) i
      calc
        dist z (c i) ≤ dist z (y i) + dist (y i) (c i) :=
          dist_triangle _ _ _
        _ ≤ r + (dist (y i) (x i) + dist (x i) (c i)) := by
          gcongr
          · simpa [Metric.mem_closedBall] using hz
          · exact dist_triangle _ _ _
        _ ≤ S + (S + S) := by gcongr; exact hr.2
        _ ≤ R := by dsimp [S]; linarith
    · rw [Function.update_of_ne hji]
      have hyj : dist (y j) (x j) ≤ S :=
        (dist_pi_le_iff hS.le).1 (Metric.mem_closedBall.1 hy) j
      have hxj : dist (x j) (c j) ≤ S :=
        (dist_pi_le_iff hS.le).1 (Metric.mem_closedBall.1 hx) j
      exact (dist_triangle _ _ _).trans
        ((add_le_add hyj hxj).trans (by dsimp [S]; linarith))
  have hnested : hartogsPolydiscIntegral (u k) x S ≤
      hartogsPolydiscIntegral (u k) c R :=
    hartogsPolydiscIntegral_mono_center (hu k) (hu0 k) hsubsets
  have hlt : V * u k x < V * ε :=
    (hmean.trans hnested).trans_lt hk
  exact (lt_of_mul_lt_mul_left hlt hV.le).le

/-- Hartogs' lemma: locally bounded nonnegative sub-mean functions that converge pointwise to
zero converge uniformly on a smaller concentric polydisc. -/
theorem hartogs_eventually_uniform_of_submean
    {n : ℕ} {u : ℕ → (Fin n → ℂ) → ℝ}
    {c : Fin n → ℂ} {R C : ℝ}
    (hR : 0 < R)
    (hu : ∀ k, ContinuousOn (u k) (closedBall c R))
    (hu0 : ∀ k x, x ∈ closedBall c R → 0 ≤ u k x)
    (hC : 0 ≤ C)
    (hub : ∀ k x, x ∈ closedBall c R → u k x ≤ C)
    (hlim : ∀ x ∈ closedBall c R,
      Tendsto (fun k ↦ u k x) atTop (nhds 0))
    (hcircle : ∀ k x, x ∈ closedBall c R → ∀ (i : Fin n) r, 0 < r →
      (∀ z ∈ closedBall (x i) r,
        Function.update x i z ∈ closedBall c R) →
      u k x ≤
        Real.circleAverage (fun z ↦ u k (Function.update x i z)) (x i) r)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ closedBall c (R / 4), u k x ≤ ε := by
  let K : Set (Fin n → ℂ) := closedBall c R
  let uk : ℕ → C(K, ℝ) := fun k ↦
    ⟨K.domRestrict (u k), (hu k).domRestrict⟩
  have hext (k : ℕ) : ∃ v : C(Fin n → ℂ, ℝ),
      (∀ x, v x ∈ Icc 0 C) ∧ ContinuousMap.restrict K v = uk k := by
    apply (uk k).exists_restrict_eq_forall_mem_of_closed
    · intro x
      exact ⟨hu0 k x x.property, hub k x x.property⟩
    · exact nonempty_Icc.2 hC
    · exact isClosed_closedBall
  choose v hv_range hv_restrict using hext
  let vfun : ℕ → (Fin n → ℂ) → ℝ := fun k ↦ v k
  have hv_eq (k : ℕ) (x : Fin n → ℂ) (hx : x ∈ closedBall c R) :
      vfun k x = u k x := by
    have h := DFunLike.congr_fun (hv_restrict k) ⟨x, hx⟩
    simpa [vfun, uk, K] using h
  have hglobal := hartogs_eventually_uniform_of_submean_global
    (u := vfun) hR
    (fun k ↦ (v k).continuous)
    (fun k x ↦ (hv_range k x).1)
    hC
    (fun k x ↦ (hv_range k x).2)
    (fun x hx ↦ by
      simpa only [hv_eq _ x hx] using hlim x hx)
    (fun k x i r hr hincl ↦ by
      have hx : x ∈ closedBall c R := by
        have hxc := hincl (x i) (by simp [hr.le])
        simpa using hxc
      rw [hv_eq k x hx]
      calc
        u k x ≤
            Real.circleAverage
              (fun z ↦ u k (Function.update x i z)) (x i) r :=
          hcircle k x hx i r hr hincl
        _ = Real.circleAverage
              (fun z ↦ vfun k (Function.update x i z)) (x i) r := by
          apply Real.circleAverage_congr_codiscreteWithin _ hr.ne'
          filter_upwards [Filter.self_mem_codiscreteWithin
            (sphere (x i) |r|)] with z hz
          apply (hv_eq k (Function.update x i z) ?_).symm
          apply hincl z
          simpa [abs_of_pos hr] using sphere_subset_closedBall hz)
    hε
  filter_upwards [hglobal] with k hk
  intro x hx
  rw [← hv_eq k x (by
    exact mem_closedBall'.2 ((mem_closedBall'.1 hx).trans (by linarith)))]
  exact hk x hx

theorem hartogs_pi_all {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : ∀ (x : Fin n → ℂ) (i : Fin n),
      Differentiable ℂ (fun z : ℂ ↦ f (Function.update x i z))) :
    Differentiable ℂ f := by
  induction n with
  | zero => exact differentiable_of_subsingleton
  | succ n ih =>
      intro x₀
      let z₀ : Fin n → ℂ := x₀ ∘ Fin.succ
      let w₀ : ℂ := x₀ 0
      let F : (Fin n → ℂ) → ℂ → ℂ := fun z w ↦ f (Fin.cons w z)
      have hx₀ : Fin.cons w₀ z₀ = x₀ := by
        funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [w₀, z₀]
      have hF₁ (w : ℂ) : Differentiable ℂ (fun z ↦ F z w) := by
        apply ih
        intro x i
        have h := hf (Fin.cons w x) i.succ
        convert h using 1
        funext t
        simp only [F, Fin.cons_update]
      have hF₂ (z : Fin n → ℂ) : Differentiable ℂ (F z) := by
        have h := hf (Fin.cons 0 z) 0
        convert h using 1
        funext t
        simp only [F, Fin.update_cons_zero]
      let K : Set (Fin n → ℂ) := closedBall z₀ 8
      obtain ⟨m, hm⟩ := hartogs_exists_interior_uniform_bound
        (f := fun w z ↦ F z w) (K := K)
        (isCompact_closedBall z₀ 8)
        (fun z _hz ↦ (hF₂ z).continuous)
        (fun w ↦ (hF₁ w).continuous.continuousOn)
      rcases hm with ⟨w₂, hw₂⟩
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior w₂ hw₂
      let B : ℝ := r / 2
      have hB : 0 < B := div_pos hr (by norm_num)
      have hbound : ∀ z ∈ closedBall z₀ 8,
          ∀ w ∈ closedBall w₂ B, ‖F z w‖ ≤ (m : ℝ) := by
        intro z hz w hw
        have hwball : w ∈ ball w₂ r := by
          rw [mem_ball]
          exact (mem_closedBall.1 hw).trans_lt (by dsimp [B]; linarith)
        exact interior_subset (hball hwball) z hz
      let s : ℝ := B / 2
      have hs : 0 < s := div_pos hB (by norm_num)
      let p : (Fin n → ℂ) → FormalMultilinearSeries ℂ ℂ ℂ :=
        fun z ↦ cauchyPowerSeries (F z) w₂ s
      let a : ℕ → (Fin n → ℂ) → ℂ := fun k z ↦ (p z).coeff k
      have ha_diff (k : ℕ) : DifferentiableOn ℂ (a k) (ball z₀ 4) := by
        convert
          differentiableOn_cauchyCoefficient_of_separately_differentiable_of_bounded
            (f := F) (z₀ := z₀) (w₀ := w₂) (A := 8) (B := B)
            (M := (m : ℝ)) (by norm_num) hB hF₁ hF₂ hbound k using 1
        · rfl
        · norm_num
      have ha_bound (k : ℕ) (z : Fin n → ℂ) (hz : z ∈ closedBall z₀ 2) :
          ‖a k z‖ ≤ (m : ℝ) * s⁻¹ ^ k := by
        apply norm_cauchyCoefficient_le hs (hF₂ z) _ k
        intro w hw
        apply hbound z
        · exact mem_closedBall'.2 ((mem_closedBall'.1 hz).trans (by norm_num))
        · rw [mem_closedBall]
          have hw' := mem_sphere.1 hw
          rw [hw']
          dsimp [s]
          linarith
      let W : ℝ := 4 * (‖w₀ - w₂‖ + 1)
      have hW : 0 < W := mul_pos (by norm_num) (by positivity)
      have hterm (z : Fin n → ℂ) :
          Tendsto (fun k ↦ ‖a k z‖ * W ^ k) atTop (nhds 0) := by
        let q : NNReal := ⟨s, hs.le⟩
        have hqs : (q : ℝ) = s := rfl
        have hq : 0 < q := by
          rw [← NNReal.coe_pos]
          rw [hqs]
          exact hs
        have hfps := (hF₂ z).hasFPowerSeriesOnBall w₂ hq
        have hsum := hfps.hasSum (y := (W : ℂ)) (by simp)
        have ht := hsum.summable.tendsto_atTop_zero.norm
        rw [hqs] at ht
        simpa [a, p,
          FormalMultilinearSeries.apply_eq_pow_smul_coeff,
          norm_smul, abs_of_pos hW, mul_comm] using ht
      let u : ℕ → (Fin n → ℂ) → ℝ := fun k z ↦
        ((k + 1 : ℕ) : ℝ)⁻¹ *
          Real.posLog (‖a (k + 1) z‖ * W ^ (k + 1))
      have hu_cont (k : ℕ) : ContinuousOn (u k) (closedBall z₀ 2) := by
        apply ContinuousOn.mul continuousOn_const
        apply Real.continuous_posLog.comp_continuousOn
        apply ContinuousOn.mul
        · apply (ha_diff (k + 1)).continuousOn.norm.mono
          intro z hz
          exact mem_ball'.2 ((mem_closedBall'.1 hz).trans_lt (by norm_num))
        · exact continuousOn_const
      have hu0 (k : ℕ) (z : Fin n → ℂ) : 0 ≤ u k z :=
        mul_nonneg (inv_nonneg.mpr (by positivity)) Real.posLog_nonneg
      let Q : ℝ := s⁻¹ * W
      have hQ : 0 < Q := mul_pos (inv_pos.mpr hs) hW
      let C : ℝ := Real.posLog (m : ℝ) + Real.posLog Q
      have hC : 0 ≤ C := add_nonneg Real.posLog_nonneg Real.posLog_nonneg
      have hu_bound (k : ℕ) (z : Fin n → ℂ)
          (hz : z ∈ closedBall z₀ 2) : u k z ≤ C := by
        let j : ℕ := k + 1
        have hjpos : (0 : ℝ) < j := by
          exact_mod_cast Nat.succ_pos k
        have hterm_bound : ‖a j z‖ * W ^ j ≤ (m : ℝ) * Q ^ j := by
          calc
            ‖a j z‖ * W ^ j ≤ ((m : ℝ) * s⁻¹ ^ j) * W ^ j :=
              mul_le_mul_of_nonneg_right (ha_bound j z hz) (pow_nonneg hW.le _)
            _ = (m : ℝ) * (s⁻¹ ^ j * W ^ j) := by ring
            _ = (m : ℝ) * (s⁻¹ * W) ^ j :=
              congrArg (fun t : ℝ ↦ (m : ℝ) * t) (mul_pow s⁻¹ W j).symm
            _ = (m : ℝ) * Q ^ j := by rfl
        have hposlog :
            Real.posLog (‖a j z‖ * W ^ j) ≤
              Real.posLog (m : ℝ) + (j : ℝ) * Real.posLog Q := by
          calc
            Real.posLog (‖a j z‖ * W ^ j) ≤
                Real.posLog ((m : ℝ) * Q ^ j) :=
              Real.posLog_le_posLog
                (by
                  have : 0 ≤ ‖a j z‖ * W ^ j :=
                    mul_nonneg (norm_nonneg _) (pow_nonneg hW.le _)
                  linarith)
                hterm_bound
            _ ≤ Real.posLog (m : ℝ) + Real.posLog (Q ^ j) :=
              Real.posLog_mul
            _ = Real.posLog (m : ℝ) +
                (j : ℝ) * Real.posLog Q := by rw [Real.posLog_pow]
        dsimp [u, C]
        change (j : ℝ)⁻¹ * Real.posLog (‖a j z‖ * W ^ j) ≤ _
        calc
          (j : ℝ)⁻¹ * Real.posLog (‖a j z‖ * W ^ j) ≤
              (j : ℝ)⁻¹ *
                (Real.posLog (m : ℝ) + (j : ℝ) * Real.posLog Q) :=
            mul_le_mul_of_nonneg_left hposlog (inv_nonneg.mpr hjpos.le)
          _ = (j : ℝ)⁻¹ * Real.posLog (m : ℝ) + Real.posLog Q := by
            field_simp [hjpos.ne']
          _ ≤ Real.posLog (m : ℝ) + Real.posLog Q := by
            have hjone : (1 : ℝ) ≤ j := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
            have hmul : (j : ℝ)⁻¹ * Real.posLog (m : ℝ) ≤
                Real.posLog (m : ℝ) := by
              calc
                _ ≤ 1 * Real.posLog (m : ℝ) :=
                  mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hjone)
                    Real.posLog_nonneg
                _ = _ := one_mul _
            exact add_le_add_left hmul _
      have hu_lim (z : Fin n → ℂ) :
          Tendsto (fun k ↦ u k z) atTop (nhds 0) := by
        have ht : Tendsto
            (fun k ↦ ‖a (k + 1) z‖ * W ^ (k + 1)) atTop (nhds 0) := by
          simpa [Nat.add_comm] using
            (Filter.tendsto_add_atTop_iff_nat 1).2 (hterm z)
        have hpl : Tendsto
            (fun k ↦ Real.posLog (‖a (k + 1) z‖ * W ^ (k + 1)))
            atTop (nhds 0) := by
          have hcomp : Tendsto
              (Real.posLog ∘ fun k ↦ ‖a (k + 1) z‖ * W ^ (k + 1))
              atTop (nhds 0) := by
            simpa only [Real.posLog_zero] using
              Real.continuous_posLog.continuousAt.tendsto.comp ht
          exact hcomp.congr' (Eventually.of_forall fun _ ↦ rfl)
        apply squeeze_zero (fun k ↦ hu0 k z) _ hpl
        intro k
        have hjone : (1 : ℝ) ≤ (k + 1 : ℕ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
        dsimp [u]
        calc
          ((k + 1 : ℕ) : ℝ)⁻¹ *
              Real.posLog (‖a (k + 1) z‖ * W ^ (k + 1)) ≤
              1 * Real.posLog (‖a (k + 1) z‖ * W ^ (k + 1)) := by
            exact mul_le_mul_of_nonneg_right
              (inv_le_one_of_one_le₀ hjone) Real.posLog_nonneg
          _ = _ := one_mul _
      have hu_circle (k : ℕ) (x : Fin n → ℂ)
          (hx : x ∈ closedBall z₀ 2) (i : Fin n) (ρ : ℝ) (hρ : 0 < ρ)
          (hincl : ∀ z ∈ closedBall (x i) ρ,
            Function.update x i z ∈ closedBall z₀ 2) :
          u k x ≤ Real.circleAverage
            (fun z ↦ u k (Function.update x i z)) (x i) ρ := by
        let j : ℕ := k + 1
        let upd : ℂ → Fin n → ℂ := fun z ↦ Function.update x i z
        have hupd : Differentiable ℂ upd := by
          rw [differentiable_pi]
          intro l
          by_cases hli : l = i
          · subst l
            simp [upd, Function.update_self]
          · have heq : (fun z ↦ upd z l) = fun _ : ℂ ↦ x l := by
              funext z
              simp [upd, Function.update_of_ne hli]
            rw [heq]
            exact differentiable_const _
        let V : Set ℂ := upd ⁻¹' ball z₀ 4
        have hVopen : IsOpen V := isOpen_ball.preimage hupd.continuous
        let g : ℂ → ℂ := fun z ↦ a j (upd z) * (W : ℂ) ^ j
        have hgdiff : DifferentiableOn ℂ g V := by
          intro z hz
          have ha_at : DifferentiableAt ℂ (a j) (upd z) :=
            (ha_diff j (upd z) hz).differentiableAt
              (isOpen_ball.mem_nhds hz)
          exact ((ha_at.comp z (hupd z)).mul_const _).differentiableWithinAt
        have hclosed : closedBall (x i) ρ ⊆ V := by
          intro z hz
          exact mem_ball'.2
            ((mem_closedBall'.1 (hincl z hz)).trans_lt (by norm_num))
        have hganalytic : AnalyticOnNhd ℂ g (closedBall (x i) ρ) :=
          (hgdiff.analyticOnNhd hVopen).mono hclosed
        have hsub := hartogs_posLog_norm_le_circleAverage hρ hganalytic
        have hsub' : Real.posLog (‖a j x‖ * W ^ j) ≤
            Real.circleAverage
              (fun z ↦ Real.posLog (‖a j (Function.update x i z)‖ * W ^ j))
              (x i) ρ := by
          simpa [g, upd, j, norm_mul, norm_pow, abs_of_pos hW,
            Function.update_eq_self, mul_comm] using hsub
        dsimp [u]
        change (j : ℝ)⁻¹ * Real.posLog (‖a j x‖ * W ^ j) ≤ _
        calc
          (j : ℝ)⁻¹ * Real.posLog (‖a j x‖ * W ^ j) ≤
              (j : ℝ)⁻¹ * Real.circleAverage
                (fun z ↦ Real.posLog
                  (‖a j (Function.update x i z)‖ * W ^ j)) (x i) ρ :=
            mul_le_mul_of_nonneg_left hsub' (inv_nonneg.mpr (by positivity))
          _ = Real.circleAverage
              (fun z ↦ (j : ℝ)⁻¹ * Real.posLog
                (‖a j (Function.update x i z)‖ * W ^ j)) (x i) ρ := by
            rw [show (fun z ↦ (j : ℝ)⁻¹ * Real.posLog
                (‖a j (Function.update x i z)‖ * W ^ j)) =
              (j : ℝ)⁻¹ • (fun z ↦ Real.posLog
                (‖a j (Function.update x i z)‖ * W ^ j)) by rfl]
            rw [Real.circleAverage_smul]
            rfl
          _ = _ := by rfl
      have huniform := hartogs_eventually_uniform_of_submean
        (u := u) (c := z₀) (R := 2) (C := C) (by norm_num)
        hu_cont (fun k z _hz ↦ hu0 k z) hC hu_bound
        (fun z _hz ↦ hu_lim z) hu_circle
        (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      have huniform' : ∀ᶠ k in atTop,
          ∀ z ∈ closedBall z₀ (1 / 2 : ℝ), u k z ≤ Real.log 2 := by
        rw [show (2 : ℝ) / 4 = 1 / 2 by norm_num] at huniform
        exact huniform
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 huniform'
      have ha_tail (k : ℕ) (hk : N ≤ k) (z : Fin n → ℂ)
          (hz : z ∈ closedBall z₀ (1 / 2 : ℝ)) :
          ‖a (k + 1) z‖ ≤ (2 / W) ^ (k + 1) := by
        let j : ℕ := k + 1
        let t : ℝ := ‖a j z‖ * W ^ j
        have hjpos : (0 : ℝ) < j := by
          exact_mod_cast Nat.succ_pos k
        have ht0 : 0 ≤ t :=
          mul_nonneg (norm_nonneg _) (pow_nonneg hW.le _)
        have hu_le := hN k hk z hz
        have hpl : Real.posLog t ≤ (j : ℝ) * Real.log 2 := by
          apply (inv_mul_le_iff₀ hjpos).1
          simpa [u, j, t] using hu_le
        have ht2 : t ≤ (2 : ℝ) ^ j := by
          by_cases ht : t ≤ 1
          · exact ht.trans (one_le_pow₀ (by norm_num))
          · have htpos : 0 < t := lt_trans (by norm_num) (lt_of_not_ge ht)
            apply (Real.strictMonoOn_log.le_iff_le htpos
              (pow_pos (by norm_num : (0 : ℝ) < 2) j)).1
            rw [Real.log_pow]
            rw [Real.posLog_eq_log (by
              rw [abs_of_nonneg ht0]
              exact (lt_of_not_ge ht).le)] at hpl
            exact hpl
        rw [div_pow]
        apply (le_div_iff₀ (pow_pos hW _)).2
        simpa [t, j] using ht2
      have hp_sum (z : Fin n → ℂ) (w : ℂ) :
          HasSum (fun j ↦ (p z j) (fun _ ↦ w - w₂)) (F z w) := by
        let q : NNReal := ⟨s, hs.le⟩
        have hqs : (q : ℝ) = s := rfl
        have hq : 0 < q := by
          rw [← NNReal.coe_pos, hqs]
          exact hs
        have hfps := (hF₂ z).hasFPowerSeriesOnBall w₂ hq
        have hsum := hfps.hasSum (y := w - w₂) (by simp)
        rw [hqs] at hsum
        simpa [p] using hsum
      let head : ℕ → ℝ := fun j ↦
        if j ≤ N then (m : ℝ) * s⁻¹ ^ j * (W / 4) ^ j else 0
      let major : ℕ → ℝ := fun j ↦ head j + (1 / 2 : ℝ) ^ j
      have hhead_support : Function.HasFiniteSupport head := by
        apply (Set.finite_Iic N).subset
        intro j hj
        by_contra hle
        have hjn : ¬j ≤ N := by simpa only [mem_Iic] using hle
        exact hj (by simp only [head, ite_eq_right hjn])
      have hmajor : Summable major := by
        apply (summable_of_hasFiniteSupport hhead_support).add
        exact summable_geometric_of_norm_lt_one (by norm_num)
      have hlocal_bound : ∀ z ∈ closedBall z₀ (1 / 2 : ℝ),
          ∀ w ∈ closedBall w₀ 1, ‖F z w‖ ≤ ∑' j, major j := by
        intro z hz w hw
        apply (hp_sum z w).norm_le_of_bounded hmajor.hasSum
        intro j
        rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, norm_smul,
          norm_pow]
        have hz2 : z ∈ closedBall z₀ 2 :=
          mem_closedBall'.2 ((mem_closedBall'.1 hz).trans (by norm_num))
        have hd : ‖w - w₂‖ ≤ W / 4 := by
          calc
            ‖w - w₂‖ ≤ ‖w - w₀‖ + ‖w₀ - w₂‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
            _ ≤ 1 + ‖w₀ - w₂‖ := by
              gcongr
              simpa [mem_closedBall, dist_eq_norm] using hw
            _ = W / 4 := by dsimp [W]; ring
        by_cases hj : j ≤ N
        · calc
            ‖w - w₂‖ ^ j * ‖(p z).coeff j‖ ≤
                (W / 4) ^ j * ((m : ℝ) * s⁻¹ ^ j) :=
              mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hd _) (ha_bound j z hz2)
                (norm_nonneg _) (pow_nonneg (by positivity) _)
            _ = (m : ℝ) * s⁻¹ ^ j * (W / 4) ^ j := by ring
            _ ≤ major j := by
              dsimp [major, head]
              rw [ite_eq_left hj]
              exact le_add_of_nonneg_right (pow_nonneg (by norm_num) _)
        · have hj0 : j ≠ 0 := by
            intro hjzero
            subst j
            exact hj (Nat.zero_le _)
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
          have hk : N ≤ k := by omega
          calc
            ‖w - w₂‖ ^ (k + 1) * ‖(p z).coeff (k + 1)‖ ≤
                (W / 4) ^ (k + 1) * (2 / W) ^ (k + 1) :=
              mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hd _)
                (ha_tail k hk z hz) (norm_nonneg _) (pow_nonneg (by positivity) _)
            _ = (1 / 2 : ℝ) ^ (k + 1) := by
              rw [← mul_pow]
              field_simp [hW.ne']
              norm_num
            _ ≤ major (k + 1) := by
              dsimp [major, head]
              rw [ite_eq_right (by omega : ¬ k + 1 ≤ N)]
              simp
      have hjoint : DifferentiableAt ℂ (Function.uncurry F) (z₀, w₀) :=
        differentiableAt_uncurry_of_separately_differentiable_of_locally_bounded
          isOpen_ball isOpen_ball hF₁ hF₂
          (fun z hz w hw ↦ hlocal_bound z (ball_subset_closedBall hz) w
            (ball_subset_closedBall hw))
          (by simp) (by simp)
      let split : (Fin (n + 1) → ℂ) → (Fin n → ℂ) × ℂ := fun x ↦
        (x ∘ Fin.succ, x 0)
      have hsplit : Differentiable ℂ split := by
        dsimp [split]
        fun_prop
      have hsplit₀ : split x₀ = (z₀, w₀) := by rfl
      have hjoint' : DifferentiableAt ℂ (Function.uncurry F) (split x₀) := by
        rw [hsplit₀]
        exact hjoint
      have hcomp := hjoint'.comp x₀ (hsplit x₀)
      convert hcomp using 1
      funext x
      dsimp [Function.uncurry, F, split]
      congr 1
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

theorem hartogs_euclidean_of_pi {n : ℕ}
    {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : Differentiable ℂ (fun x : Fin n → ℂ => f (WithLp.toLp 2 x))) :
    Differentiable ℂ f := by
  let e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) :=
    EuclideanSpace.equiv (Fin n) ℂ
  have he : Differentiable ℂ (e : EuclideanSpace ℂ (Fin n) → Fin n → ℂ) :=
    e.toContinuousLinearMap.differentiable
  have hf' : Differentiable ℂ (fun x : Fin n → ℂ => f (e.symm x)) := by
    simpa [e] using hf
  have hcomp := hf'.comp he
  convert hcomp using 1
  funext x
  change f x = f (e.symm (e x))
  rw [e.symm_apply_apply]

/--
If `f : ℂⁿ → ℂ` is entire in each variable separately via `Function.update` slices, then `f` is
jointly `Differentiable ℂ` on `ℂⁿ`. Source: Hartogs separate analyticity (Osgood–Hartogs); see
Hörmander; Lean is scalar-valued entire separately holomorphic via Function.update slices implies
jointly Differentiable ℂ, finite-dimensional ℂⁿ specialization.

Proves `Wanted` entry `hartogs_separate_analyticity`.

Proof: induction on the number of variables. Baire category gives a polydisc where `f` is
bounded, where Osgood's lemma makes it holomorphic; Hartogs' lemma on sub-mean-value functions
then makes the Cauchy expansion in the last variable converge locally uniformly.
-/
theorem hartogs_separate_analyticity
    {n : ℕ}
    {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : ∀ (x : EuclideanSpace ℂ (Fin n)) (i : Fin n),
      Differentiable ℂ (fun z : ℂ =>
        f (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i z)))) :
    Differentiable ℂ f := by
  apply hartogs_euclidean_of_pi
  apply hartogs_pi_all
  intro x i
  simpa using hf (WithLp.toLp 2 x) i

end Complex.HartogsWanted
