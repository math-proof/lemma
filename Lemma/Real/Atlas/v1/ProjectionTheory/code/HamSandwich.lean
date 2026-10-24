import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProjectionTheory.code.HamSandwich
open MeasureTheory InnerProductSpace Set Filter Topology HamSandwich


namespace HamSandwich

/--
[extractNormal_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HamSandwich.lean)
-/
@[path]
lemma extractNormal_neg
  {n : ℕ}
  {θ : EuclideanSpace ℝ (Fin (n + 1))} :
-- imply
  extractNormal n (-θ) = -extractNormal n θ := by
-- proof
  simp only [extractNormal, EuclideanSpace.equiv, PiLp.neg_apply]
  ext i; simp [PiLp.neg_apply]

end HamSandwich

namespace HamSandwich

/--
[extractOffset_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HamSandwich.lean)
-/
@[path]
lemma extractOffset_neg
  {n : ℕ}
  {θ : EuclideanSpace ℝ (Fin (n + 1))} :
-- imply
  extractOffset n (-θ) = -extractOffset n θ := by
-- proof
  simp [extractOffset, PiLp.neg_apply]

end HamSandwich

namespace HamSandwich

/--
[affineFunctional_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HamSandwich.lean)
-/
@[path]
lemma affineFunctional_neg
  {n : ℕ}
  {θ : EuclideanSpace ℝ (Fin (n + 1))}
  {x : EuclideanSpace ℝ (Fin n)} :
-- imply
  affineFunctional n (-θ) x = -affineFunctional n θ x := by
-- proof
  simp [affineFunctional, extractNormal_neg, extractOffset_neg, inner_neg_left]; ring

end HamSandwich

namespace HamSandwich

/--
[continuous_extractNormal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HamSandwich.lean)
-/
@[path]
lemma continuous_extractNormal
  {n : ℕ} :
-- imply
  Continuous (extractNormal n) :=
-- proof
  (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp
    (continuous_pi (fun i => PiLp.continuous_apply 2 (fun _ => ℝ) (Fin.castSucc i)))

end HamSandwich

namespace HamSandwich

/--
[continuous_extractOffset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HamSandwich.lean)
-/
@[path]
lemma continuous_extractOffset
  {n : ℕ} :
-- imply
  Continuous (extractOffset n) :=
-- proof
  PiLp.continuous_apply 2 (fun _ => ℝ) (Fin.last n)

end HamSandwich

namespace HamSandwich

/--
[continuousAt_affineFunctional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HamSandwich.lean)
-/
@[path]
lemma continuousAt_affineFunctional
  {n : ℕ}
  {x : EuclideanSpace ℝ (Fin n)}
  {θ₀ : EuclideanSpace ℝ (Fin (n + 1))} :
-- imply
  ContinuousAt (fun θ => affineFunctional n θ x) θ₀ :=
-- proof
  (((continuous_extractNormal n).inner continuous_const).sub
    (continuous_extractOffset n)).continuousAt

end HamSandwich

namespace HamSandwich

/--
[continuous_affineFunctional_x](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HamSandwich.lean)
-/
@[path]
lemma continuous_affineFunctional_x
  {n : ℕ}
  {θ : EuclideanSpace ℝ (Fin (n + 1))} :
-- imply
  Continuous (affineFunctional n θ) :=
-- proof
  (continuous_const.inner continuous_id).sub continuous_const

end HamSandwich

namespace HamSandwich

/--
[isOpen_halfSpace_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HamSandwich.lean)
-/
@[path]
lemma isOpen_halfSpace_pos
  {n : ℕ}
  {θ : EuclideanSpace ℝ (Fin (n + 1))} :
-- imply
  IsOpen {y : EuclideanSpace ℝ (Fin n) | affineFunctional n θ y > 0} :=
-- proof
  isOpen_lt continuous_const (continuous_affineFunctional_x n θ)

end HamSandwich

namespace HamSandwich

/--
[indicator_halfspace_continuousAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HamSandwich.lean)
-/
@[path]
lemma indicator_halfspace_continuousAt
  {n : ℕ}
  {θ₀ : EuclideanSpace ℝ (Fin (n + 1))}
  {x : EuclideanSpace ℝ (Fin n)}
-- given
  (hx : affineFunctional n θ₀ x ≠ 0) :
-- imply
  ContinuousAt (fun θ => Set.indicator {y : EuclideanSpace ℝ (Fin n) | affineFunctional n θ y > 0} (fun _ => (1 : ℝ)) x) θ₀ := by
-- proof
  rw [ContinuousAt]
  obtain h | h := lt_or_gt_of_ne hx
  · rw [show Set.indicator {y | affineFunctional n θ₀ y > 0} (fun _ => (1 : ℝ)) x = 0 from by
    simp only [indicator_apply, mem_setOf_eq, if_neg (not_lt.mpr (le_of_lt h))]]
    exact tendsto_nhds_of_eventually_eq (by
      filter_upwards [(continuousAt_affineFunctional n x θ₀).eventually (Iio_mem_nhds h)]
        with θ hθ
      simp only [indicator_apply, mem_setOf_eq, if_neg (not_lt.mpr (le_of_lt hθ))])
  · rw [show Set.indicator {y | affineFunctional n θ₀ y > 0} (fun _ => (1 : ℝ)) x = 1 from by
    simp only [indicator_apply, mem_setOf_eq, if_pos h]]
    exact tendsto_nhds_of_eventually_eq (by
      filter_upwards [(continuousAt_affineFunctional n x θ₀).eventually (Ioi_mem_nhds h)]
        with θ hθ
      simp only [indicator_apply, mem_setOf_eq, if_pos hθ])

end HamSandwich

namespace HamSandwich

/--
[hyperplane_measure_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HamSandwich.lean)
-/
@[path]
lemma hyperplane_measure_zero
  {n : ℕ}
  {v : EuclideanSpace ℝ (Fin n)}
  {c : ℝ}
-- given
  (hv : v ≠ 0) :
-- imply
  volume {x : EuclideanSpace ℝ (Fin n) | ⟪v, x⟫_ℝ = c} = 0 := by
-- proof
  set f := (innerSL (𝕜 := ℝ) v).toLinearMap
  have hfv : ∀ x, f x = ⟪v, x⟫_ℝ := fun x => by simp [f]
  have hker : LinearMap.ker f ≠ ⊤ := by
    intro h; apply hv
    have hmem : v ∈ LinearMap.ker f := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hfv, real_inner_self_eq_norm_sq, sq_eq_zero_iff,
      norm_eq_zero] at hmem
    exact hmem
  by_cases hex : ∃ x₀ : EuclideanSpace ℝ (Fin n), ⟪v, x₀⟫_ℝ = c
  · obtain ⟨x₀, hx₀⟩ := hex
    have heq : {x : EuclideanSpace ℝ (Fin n) | ⟪v, x⟫_ℝ = c} =
      (x₀ +ᵥ ·) '' (LinearMap.ker f : Set (EuclideanSpace ℝ (Fin n))) := by
      ext x
      simp only [mem_setOf_eq, mem_image, SetLike.mem_coe, LinearMap.mem_ker, hfv]
      exact ⟨fun hx => ⟨x - x₀, by rw [inner_sub_right]; linarith, by simp [vadd_eq_add]⟩,
        fun ⟨y, hy, hyx⟩ => by rw [← hyx, vadd_eq_add, inner_add_right, hy, add_zero]; exact hx₀⟩
    rw [heq, image_vadd, measure_vadd]
    exact Measure.addHaar_submodule volume _ hker
  · have hempty : {x : EuclideanSpace ℝ (Fin n) | ⟪v, x⟫_ℝ = c} = ∅ := by
    ext x; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    exact fun hx => hex ⟨x, hx⟩
    rw [hempty, measure_empty]

end HamSandwich

namespace HamSandwich

/--
[ae_affineFunctional_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HamSandwich.lean)
-/
@[path]
lemma ae_affineFunctional_ne_zero
  {n : ℕ}
  {θ₀ : EuclideanSpace ℝ (Fin (n + 1))}
  {A : Set (EuclideanSpace ℝ (Fin n))}
-- given
  (hθ : θ₀ ≠ 0) :
-- imply
  ∀ᵐ x ∂(volume.restrict A), affineFunctional n θ₀ x ≠ 0 := by
-- proof
  suffices h : volume {x : EuclideanSpace ℝ (Fin n) | affineFunctional n θ₀ x = 0} = 0 by
    apply ae_restrict_of_ae; rw [ae_iff]; simp only [not_not]
    exact measure_mono_null (fun x hx => hx) h
  have heq : {x : EuclideanSpace ℝ (Fin n) | affineFunctional n θ₀ x = 0} =
    {x | ⟪extractNormal n θ₀, x⟫_ℝ = extractOffset n θ₀} := by
    ext x; simp [affineFunctional, sub_eq_zero]
  rw [heq]
  by_cases hv : extractNormal n θ₀ = 0
  · have hc : extractOffset n θ₀ ≠ 0 := by
    intro hc; apply hθ; ext i
    by_cases hi : i = Fin.last n
    · subst hi; exact hc
    · have hij := Fin.exists_castSucc_eq.mpr hi
      obtain ⟨j, rfl⟩ := hij
      have : (extractNormal n θ₀) j = 0 := by rw [hv]; rfl
      simpa [extractNormal, EuclideanSpace.equiv] using this
    have : {x : EuclideanSpace ℝ (Fin n) | ⟪extractNormal n θ₀, x⟫_ℝ = extractOffset n θ₀} = ∅ := by
      ext x; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, hv, inner_zero_left]
      exact fun hx => hc hx.symm
    rw [this, measure_empty]
  · exact hyperplane_measure_zero _ _ hv

end HamSandwich

namespace HamSandwich

/--
[continuousAt_volume_halfspace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HamSandwich.lean)
-/
@[path]
lemma continuousAt_volume_halfspace
  {n : ℕ}
  {A : Set (EuclideanSpace ℝ (Fin n))}
  {θ₀ : EuclideanSpace ℝ (Fin (n + 1))}
-- given
  (hBdd : Bornology.IsBounded A)
  (hθ : θ₀ ≠ 0) :
-- imply
  ContinuousAt (fun θ : EuclideanSpace ℝ (Fin (n + 1)) => ∫ x in A, Set.indicator {y : EuclideanSpace ℝ (Fin n) | affineFunctional n θ y > 0} (fun _ => (1 : ℝ)) x ∂volume) θ₀ := by
-- proof
  haveI : IsFiniteMeasure (volume.restrict A) :=
    isFiniteMeasure_restrict.mpr (hBdd.measure_lt_top.ne)
  apply continuousAt_of_dominated (bound := fun _ => (1 : ℝ))
  · apply Eventually.of_forall; intro θ
    exact (stronglyMeasurable_const.indicator
      (isOpen_halfSpace_pos n θ).measurableSet).aestronglyMeasurable
  · apply Eventually.of_forall; intro θ
    apply Eventually.of_forall; intro x
    unfold Set.indicator; split_ifs <;> simp
  · exact integrable_const 1
  · exact (ae_affineFunctional_ne_zero n θ₀ hθ A).mono
    (fun x hx => indicator_halfspace_continuousAt n θ₀ x hx)

end HamSandwich

namespace HamSandwich

/--
[continuousAt_volume_halfspace_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HamSandwich.lean)
-/
@[path]
lemma continuousAt_volume_halfspace_neg
  {n : ℕ}
  {A : Set (EuclideanSpace ℝ (Fin n))}
  {θ₀ : EuclideanSpace ℝ (Fin (n + 1))}
-- given
  (hBdd : Bornology.IsBounded A)
  (hθ : θ₀ ≠ 0) :
-- imply
  ContinuousAt (fun θ : EuclideanSpace ℝ (Fin (n + 1)) => ∫ x in A, Set.indicator {y : EuclideanSpace ℝ (Fin n) | affineFunctional n θ y < 0} (fun _ => (1 : ℝ)) x ∂volume) θ₀ := by
-- proof
  haveI : IsFiniteMeasure (volume.restrict A) :=
    isFiniteMeasure_restrict.mpr (hBdd.measure_lt_top.ne)
  apply continuousAt_of_dominated (bound := fun _ => (1 : ℝ))
  · apply Eventually.of_forall; intro θ
    exact (stronglyMeasurable_const.indicator
      (isOpen_lt (continuous_affineFunctional_x n θ) continuous_const).measurableSet).aestronglyMeasurable
  · apply Eventually.of_forall; intro θ
    apply Eventually.of_forall; intro x
    unfold Set.indicator; split_ifs <;> simp
  · exact integrable_const 1
  ·
    apply (ae_affineFunctional_ne_zero n θ₀ hθ A).mono
    intro x hx
    rw [ContinuousAt]
    obtain h | h := lt_or_gt_of_ne hx
    ·
      rw [show Set.indicator {y | affineFunctional n θ₀ y < 0} (fun _ => (1 : ℝ)) x = 1 from by
        simp only [indicator_apply, mem_setOf_eq, if_pos h]]
      exact tendsto_nhds_of_eventually_eq (by
        filter_upwards [(continuousAt_affineFunctional n x θ₀).eventually (Iio_mem_nhds h)]
          with θ hθ
        simp only [indicator_apply, mem_setOf_eq, if_pos hθ])
    ·
      rw [show Set.indicator {y | affineFunctional n θ₀ y < 0} (fun _ => (1 : ℝ)) x = 0 from by
        simp only [indicator_apply, mem_setOf_eq, if_neg (not_lt.mpr (le_of_lt h))]]
      exact tendsto_nhds_of_eventually_eq (by
        filter_upwards [(continuousAt_affineFunctional n x θ₀).eventually (Ioi_mem_nhds h)]
          with θ hθ
        simp only [indicator_apply, mem_setOf_eq, if_neg (not_lt.mpr (le_of_lt hθ))])

end HamSandwich

namespace HamSandwich

/--
[integral_indicator_eq_volume](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HamSandwich.lean)
-/
@[path]
lemma integral_indicator_eq_volume
  {n : ℕ}
  {A S : Set (EuclideanSpace ℝ (Fin n))}
-- given
  (hS : MeasurableSet S) :
-- imply
  ∫ x in A, S.indicator (fun _ => (1 : ℝ)) x ∂volume = (volume (A ∩ S)).toReal := by
-- proof
  rw [integral_indicator hS, Measure.restrict_restrict hS, inter_comm]
  simp [Measure.real]

end HamSandwich

namespace HamSandwich

/--
[ham_sandwich_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HamSandwich.lean)
-/
@[path]
lemma ham_sandwich_theorem
  {n : ℕ}
  {A : Fin n → Set (EuclideanSpace ℝ (Fin n))}
-- given
  (hOpen : ∀ i, IsOpen (A i))
  (hBdd : ∀ i, Bornology.IsBounded (A i))
  (hNe : ∀ i, (A i).Nonempty)
  (hn : 0 < n) :
-- imply
  ∃ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ), v ≠ 0 ∧ ∀ i, Bisects n v c (A i) := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set f_raw : ↥(BorsukUlam.Sphere (m + 1)) → EuclideanSpace ℝ (Fin (m + 1)) :=
    fun θ => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (fun i =>
      (∫ x in (A i), indicator {y | affineFunctional (m+1) θ.val y > 0} (fun _ => (1:ℝ)) x) -
      (∫ x in (A i), indicator {y | affineFunctional (m+1) θ.val y < 0} (fun _ => (1:ℝ)) x))
  have hf_cont : Continuous f_raw := by
    rw [continuous_iff_continuousAt]; intro ⟨θ, hθ⟩
    have hne : θ ≠ 0 := by
      simp only [BorsukUlam.Sphere, Metric.mem_sphere, dist_zero_right] at hθ
      intro h; simp [h] at hθ
    simp only [f_raw, ContinuousAt]
    apply Filter.Tendsto.comp (y := nhds _)
    · exact (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm.continuous.continuousAt.tendsto
    · apply tendsto_pi_nhds.mpr; intro i
      exact ((continuousAt_volume_halfspace (m+1) (A i) (hBdd i) θ hne).sub
        (continuousAt_volume_halfspace_neg (m+1) (A i) (hBdd i) θ hne)).tendsto.comp
        (continuous_subtype_val.continuousAt.tendsto)
  have hf_anti : ∀ θ : ↥(BorsukUlam.Sphere (m + 1)),
    f_raw θ = -f_raw ⟨-θ.val, BorsukUlam.neg_mem_sphere θ.property⟩ := by
    intro ⟨θ, hθ⟩; simp only [f_raw]
    have h_pos : {y | affineFunctional (m+1) (-θ) y > 0} = {y | affineFunctional (m+1) θ y < 0} := by
      ext y; simp [affineFunctional_neg, neg_pos]
    have h_neg : {y | affineFunctional (m+1) (-θ) y < 0} = {y | affineFunctional (m+1) θ y > 0} := by
      ext y; simp [affineFunctional_neg, neg_lt_zero]
    simp only [h_pos, h_neg]
    ext i
    simp [EuclideanSpace.equiv, PiLp.neg_apply, Pi.neg_apply, WithLp.equiv]
  let f : C(↥(BorsukUlam.Sphere (m + 1)), EuclideanSpace ℝ (Fin (m + 1))) :=
    ⟨f_raw, hf_cont⟩
  obtain ⟨θ₀, hθ₀⟩ := BorsukUlam.borsuk_ulam (m + 1) f hf_anti
  refine ⟨extractNormal (m + 1) θ₀.val, extractOffset (m + 1) θ₀.val, ?_, ?_⟩
  ·
    intro hv
    have hθ_sphere := θ₀.property
    simp only [BorsukUlam.Sphere, Metric.mem_sphere, dist_zero_right] at hθ_sphere
    have hf_zero : ∀ i : Fin (m+1),
      (∫ x in (A i), indicator {y | affineFunctional (m+1) θ₀.val y > 0} (fun _ => (1:ℝ)) x) =
      (∫ x in (A i), indicator {y | affineFunctional (m+1) θ₀.val y < 0} (fun _ => (1:ℝ)) x) := by
      intro i
      have h := congr_arg (fun v => (EuclideanSpace.equiv (Fin (m+1)) ℝ) v i) hθ₀
      simp [f, f_raw] at h
      linarith
    have hc : extractOffset (m+1) θ₀.val ≠ 0 := by
      intro hc; have : θ₀.val = 0 := by
        ext i; by_cases hi : i = Fin.last (m + 1)
        · subst hi; exact hc
        · have hij := Fin.exists_castSucc_eq.mpr hi
          obtain ⟨j, rfl⟩ := hij
          have : (extractNormal (m+1) θ₀.val) j = 0 := by rw [hv]; rfl
          simpa [extractNormal, EuclideanSpace.equiv] using this
      simp [this] at hθ_sphere
    have haff : ∀ y, affineFunctional (m+1) θ₀.val y = -(extractOffset (m+1) θ₀.val) := by
      intro y; simp [affineFunctional, hv, inner_zero_left]
    specialize hf_zero ⟨0, by omega⟩
    obtain hc_neg | hc_pos := lt_or_gt_of_ne hc
    · have h1 : {y : EuclideanSpace ℝ (Fin (m+1)) | affineFunctional (m+1) θ₀.val y > 0} = univ := by
      ext y; simp [haff, neg_pos.mpr hc_neg]
      have h2 : {y : EuclideanSpace ℝ (Fin (m+1)) | affineFunctional (m+1) θ₀.val y < 0} = ∅ := by
        ext y; simp [haff]; linarith
      rw [h1, h2] at hf_zero
      simp [indicator_univ, indicator_empty] at hf_zero
      have hpos := IsOpen.measure_pos volume (hOpen ⟨0, by omega⟩) (hNe ⟨0, by omega⟩)
      have hfin := (hBdd ⟨0, by omega⟩).measure_lt_top (μ := (volume : Measure (EuclideanSpace ℝ (Fin (m+1)))))
      have hreal := ENNReal.toReal_pos hpos.ne' hfin.ne
      rw [show (0 : Fin (m+1)) = ⟨0, hn⟩ from rfl] at hf_zero
      rw [Measure.real] at hf_zero
      linarith
    · have h1 : {y : EuclideanSpace ℝ (Fin (m+1)) | affineFunctional (m+1) θ₀.val y > 0} = ∅ := by
      ext y; simp [haff]; linarith
      have h2 : {y : EuclideanSpace ℝ (Fin (m+1)) | affineFunctional (m+1) θ₀.val y < 0} = univ := by
        ext y; simp [haff, neg_lt_zero.mpr hc_pos]
      rw [h1, h2] at hf_zero
      simp [indicator_univ, indicator_empty] at hf_zero
      have hpos := IsOpen.measure_pos volume (hOpen ⟨0, by omega⟩) (hNe ⟨0, by omega⟩)
      have hfin := (hBdd ⟨0, by omega⟩).measure_lt_top (μ := (volume : Measure (EuclideanSpace ℝ (Fin (m+1)))))
      have hreal := ENNReal.toReal_pos hpos.ne' hfin.ne
      rw [show (0 : Fin (m+1)) = ⟨0, hn⟩ from rfl] at hf_zero
      rw [Measure.real] at hf_zero
      linarith
  ·
    intro i
    unfold Bisects halfSpaceBelow halfSpaceAbove
    have hf_zero_i :
      (∫ x in (A i), indicator {y | affineFunctional (m+1) θ₀.val y > 0} (fun _ => (1:ℝ)) x) =
      (∫ x in (A i), indicator {y | affineFunctional (m+1) θ₀.val y < 0} (fun _ => (1:ℝ)) x) := by
      have h := congr_arg (fun v => (EuclideanSpace.equiv (Fin (m+1)) ℝ) v i) hθ₀
      simp [f, f_raw] at h
      linarith
    have hS_pos : MeasurableSet {y : EuclideanSpace ℝ (Fin (m+1)) | affineFunctional (m+1) θ₀.val y > 0} :=
      (isOpen_halfSpace_pos (m+1) θ₀.val).measurableSet
    have hS_neg : MeasurableSet {y : EuclideanSpace ℝ (Fin (m+1)) | affineFunctional (m+1) θ₀.val y < 0} :=
      (isOpen_lt (continuous_affineFunctional_x (m+1) θ₀.val) continuous_const).measurableSet
    rw [integral_indicator_eq_volume (A i) _ hS_pos,
      integral_indicator_eq_volume (A i) _ hS_neg] at hf_zero_i
    have h_above : {y : EuclideanSpace ℝ (Fin (m+1)) | affineFunctional (m+1) θ₀.val y > 0} =
      halfSpaceAbove (m+1) (extractNormal (m+1) θ₀.val) (extractOffset (m+1) θ₀.val) := by
      ext y; simp [affineFunctional, halfSpaceAbove, sub_pos]
    have h_below : {y : EuclideanSpace ℝ (Fin (m+1)) | affineFunctional (m+1) θ₀.val y < 0} =
      halfSpaceBelow (m+1) (extractNormal (m+1) θ₀.val) (extractOffset (m+1) θ₀.val) := by
      ext y; simp [affineFunctional, halfSpaceBelow, sub_neg]
    rw [h_above, h_below] at hf_zero_i
    have hfin1 : volume (A i ∩ halfSpaceAbove (m+1) (extractNormal (m+1) θ₀.val) (extractOffset (m+1) θ₀.val)) < ⊤ :=
      lt_of_le_of_lt (measure_mono inter_subset_left) (hBdd i).measure_lt_top
    have hfin2 : volume (A i ∩ halfSpaceBelow (m+1) (extractNormal (m+1) θ₀.val) (extractOffset (m+1) θ₀.val)) < ⊤ :=
      lt_of_le_of_lt (measure_mono inter_subset_left) (hBdd i).measure_lt_top
    exact (ENNReal.toReal_eq_toReal hfin2.ne hfin1.ne).mp hf_zero_i.symm
end



-- created on 2026-10-23
