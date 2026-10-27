import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.Normed.Series.NormalConvergence
import Lemma.Real.NormalConvergence
open Set Metric Filter Topology ENNReal


/--
[ConvergesNormallyOn.summable_toReal_supNormOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/NormalConvergence.lean)
-/
@[path]
lemma ConvergesNormallyOn.summable_toReal_supNormOn
  [SeminormedAddCommGroup E]
  {f : ℕ → X → E}
  {S : Set X}
-- given
  (hf : ConvergesNormallyOn f S) :
-- imply
  Summable (fun n => (supNormOn (f n) S).toReal) :=
-- proof
  ENNReal.summable_toReal hf

/--
[ConvergesNormallyOn.summable_norm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/NormalConvergence.lean)
-/
@[path]
lemma ConvergesNormallyOn.summable_norm
  [SeminormedAddCommGroup E]
  {f : Nat → X → E}
  {S : Set X}
  {x : X}
-- given
  (hf : ConvergesNormallyOn f S)
  (hx : x ∈ S) :
-- imply
  Summable (fun n => norm (f n x)) := by
-- proof
  have hsum := hf.summable_toReal_supNormOn
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => by
      rw [← ENNReal.ofReal_le_iff_le_toReal (ENNReal.ne_top_of_tsum_ne_top hf n)]
      exact le_iSup (fun y : S => ENNReal.ofReal ‖f n ↑y‖) ⟨x, hx⟩)
    hsum

/--
[ConvergesLocallyNormallyOn.summable_norm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/NormalConvergence.lean)
-/
@[path]
lemma ConvergesLocallyNormallyOn.summable_norm
  [TopologicalSpace X] [SeminormedAddCommGroup E]
  {f : Nat → X → E}
  {S : Set X}
  {x : X}
-- given
  (hf : ConvergesLocallyNormallyOn f S)
  (hx : x ∈ S) :
-- imply
  Summable (fun n => norm (f n x)) := by
-- proof
  obtain ⟨U, hU, hnormal⟩ := hf x hx
  have hxU : x ∈ U := mem_of_mem_nhds hU
  exact hnormal.summable_norm ⟨hxU, hx⟩

/--
[ConvergesNormallyOn.tendstoUniformlyOn_tsum_nat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/NormalConvergence.lean)
-/
@[path]
lemma ConvergesNormallyOn.tendstoUniformlyOn_tsum_nat
  [NormedAddCommGroup E] [CompleteSpace E]
  {f : ℕ → X → E}
  {S : Set X}
-- given
  (hf : ConvergesNormallyOn f S) :
-- imply
  TendstoUniformlyOn (fun N z => ∑ n ∈ Finset.range N, f n z)
    (fun z => ∑' n, f n z) atTop S := by
-- proof
  have hsum : Summable (fun n => (supNormOn (f n) S).toReal) :=
    hf.summable_toReal_supNormOn
  apply _root_.tendstoUniformlyOn_tsum_nat hsum
  intro n z hz
  have hle : ENNReal.ofReal ‖f n z‖ ≤ supNormOn (f n) S := by
    unfold supNormOn
    exact le_iSup (fun x : S => ENNReal.ofReal ‖f n x‖) ⟨z, hz⟩
  exact (ENNReal.ofReal_le_iff_le_toReal
    (ENNReal.ne_top_of_tsum_ne_top hf n)).mp hle

/--
[ConvergesLocallyNormallyOn.deriv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/NormalConvergence.lean)
-/
@[path]
lemma ConvergesLocallyNormallyOn.deriv
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℕ → ℂ → E}
  {S : Set ℂ}
-- given
  (hf : ConvergesLocallyNormallyOn f S)
  (hS : IsOpen S)
  (holo : ∀ n, DifferentiableOn ℂ (f n) S) :
-- imply
  ConvergesLocallyNormallyOn (fun n z => _root_.deriv (f n) z) S := by
-- proof
  intro z₀ hz₀
  obtain ⟨U, hU, hUnorm⟩ := hf z₀ hz₀
  obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
  have hVSopen : IsOpen (V ∩ S) := hVopen.inter hS
  have hzVS : z₀ ∈ V ∩ S := ⟨hzV, hz₀⟩
  obtain ⟨r, hrpos, hball⟩ := Metric.isOpen_iff.mp hVSopen z₀ hzVS
  set s : ℝ := r / 4 with hs
  have hspos : 0 < s := by positivity
  refine ⟨ball z₀ s, ball_mem_nhds z₀ hspos, ?_⟩
  have hCfin : ∀ n, supNormOn (f n) (U ∩ S) ≠ ⊤ :=
    ENNReal.ne_top_of_tsum_ne_top hUnorm
  have hderiv_sup : ∀ n, supNormOn (fun z => _root_.deriv (f n) z) (ball z₀ s)
    ≤ supNormOn (f n) (U ∩ S) / ENNReal.ofReal s := by
    intro n
    apply iSup_le
    rintro ⟨z, hz⟩
    have hcb_sub : closedBall z s ⊆ U ∩ S := by
      intro w hw
      apply Set.inter_subset_inter_left S hVU
      apply hball
      rw [mem_ball]
      calc
        dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ ≤ s + dist z z₀ := by linarith [mem_closedBall.mp hw]
        _ < s + s := by linarith [mem_ball.mp hz]
        _ = r / 2 := by rw [hs]; ring
        _ < r := by linarith
    have hdiff : DiffContOnCl ℂ (f n) (ball z s) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball z (ne_of_gt hspos)]
      exact (holo n).mono (hcb_sub.trans inter_subset_right)
    have hbound : ∀ w ∈ sphere z s,
      ‖f n w‖ ≤ (supNormOn (f n) (U ∩ S)).toReal := by
      intro w hw
      have hwUS : w ∈ U ∩ S := hcb_sub (sphere_subset_closedBall hw)
      apply (ENNReal.ofReal_le_iff_le_toReal (hCfin n)).mp
      unfold supNormOn
      exact le_iSup (fun x : ↥(U ∩ S) => ENNReal.ofReal ‖f n x‖) ⟨w, hwUS⟩
    have hle : ‖_root_.deriv (f n) z‖ ≤ (supNormOn (f n) (U ∩ S)).toReal / s :=
      Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hspos hdiff hbound
    calc
      ENNReal.ofReal ‖_root_.deriv (f n) z‖
        ≤ ENNReal.ofReal ((supNormOn (f n) (U ∩ S)).toReal / s) :=
        ENNReal.ofReal_le_ofReal hle
      _ = supNormOn (f n) (U ∩ S) / ENNReal.ofReal s := by
        rw [ENNReal.ofReal_div_of_pos hspos, ENNReal.ofReal_toReal (hCfin n)]
  have hsum : ∑' n, (supNormOn (f n) (U ∩ S) / ENNReal.ofReal s) ≠ ⊤ := by
    simp_rw [div_eq_mul_inv, ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top hUnorm
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hspos))
  have hderiv_sup' : ∀ n, supNormOn (fun z => _root_.deriv (f n) z) (ball z₀ s ∩ S)
    ≤ supNormOn (f n) (U ∩ S) / ENNReal.ofReal s :=
    fun n => le_trans (supNormOn_mono Set.inter_subset_left _) (hderiv_sup n)
  exact ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hderiv_sup')

/--
[ConvergesLocallyNormallyOn.tendstoLocallyUniformlyOn_tsum_nat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/NormalConvergence.lean)
-/
@[path]
lemma ConvergesLocallyNormallyOn.tendstoLocallyUniformlyOn_tsum_nat
  [TopologicalSpace X] [NormedAddCommGroup E] [CompleteSpace E]
  {f : Nat → X → E}
  {S : Set X}
-- given
  (hf : ConvergesLocallyNormallyOn f S) :
-- imply
  TendstoLocallyUniformlyOn
    (fun N x => Finset.sum (Finset.range N) fun n => f n x)
    (fun x => ∑' n, f n x) atTop S := by
-- proof
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro x hx
  obtain ⟨U, hU, hnormal⟩ := hf x hx
  refine ⟨U ∩ S, ?_, hnormal.tendstoUniformlyOn_tsum_nat⟩
  simpa only [inter_comm] using inter_mem_nhdsWithin S hU

/--
[ConvergesLocallyNormallyOn.hasDerivAt_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/NormalConvergence.lean)
-/
@[path]
lemma ConvergesLocallyNormallyOn.hasDerivAt_tsum
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : Nat → Complex → E}
  {S : Set Complex}
  {z : Complex}
-- given
  (hf : ConvergesLocallyNormallyOn f S)
  (hS : IsOpen S)
  (holo : ∀ n, DifferentiableOn Complex (f n) S)
  (hz : z ∈ S) :
-- imply
  HasDerivAt (fun w => ∑' n, f n w) (∑' n, _root_.deriv (f n) z) z := by
-- proof
  have hderiv_conv := hf.deriv hS holo
  have hderiv_unif := hderiv_conv.tendstoLocallyUniformlyOn_tsum_nat
  have hderiv_eq : ∀ N w, w ∈ S →
    _root_.deriv (fun z => Finset.sum (Finset.range N) fun k => f k z) w =
      Finset.sum (Finset.range N) fun k => _root_.deriv (f k) w := by
    intro N w hw
    have hfun : (fun z => Finset.sum (Finset.range N) fun k => f k z) =
      Finset.sum (Finset.range N) fun k => f k := by
      ext z
      simp [Finset.sum_apply]
    rw [hfun]
    exact deriv_sum (fun k _ => (holo k w hw).differentiableAt (hS.mem_nhds hw))
  have hderiv_comp : TendstoLocallyUniformlyOn
    (fun N w => _root_.deriv (fun z => Finset.sum (Finset.range N) fun k => f k z) w)
    (fun w => ∑' n, _root_.deriv (f n) w) atTop S :=
    hderiv_unif.congr (fun N w hw => (hderiv_eq N w hw).symm)
  have hpartial_holo : ∀ᶠ N in atTop,
    DifferentiableOn Complex (fun z => Finset.sum (Finset.range N) fun k => f k z) S := by
    apply Filter.Eventually.of_forall
    intro N
    have h1 : (fun z => Finset.sum (Finset.range N) fun k => f k z) =
      Finset.sum (Finset.range N) fun k => f k := by
      ext z
      simp [Finset.sum_apply]
    rw [h1]
    exact DifferentiableOn.sum (fun k _ => holo k)
  have hpointwise : ∀ w ∈ S,
    Tendsto (fun N => Finset.sum (Finset.range N) fun k => f k w) atTop
      (𝓝 (∑' n, f n w)) := by
    intro w hw
    exact (hf.tendstoLocallyUniformlyOn_tsum_nat).tendsto_at hw
  exact hasDerivAt_of_tendsto_locally_uniformly_on' hS hderiv_comp
    hpartial_holo hpointwise hz


-- created on 2026-10-20
-- updated on 2026-10-26
