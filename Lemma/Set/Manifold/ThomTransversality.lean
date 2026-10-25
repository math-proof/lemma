import Mathlib
import sympy.Basic
import Theorem.Geometry.Manifold.ThomTransversality
open scoped Manifold
open MathlibExt.Geometry.Manifold.ThomTransversalityWanted


namespace MathlibExt.Geometry.Manifold.ThomTransversalityWanted

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M] [CompactSpace M] [SecondCountableTopology M]
/--
[sard_critical_values_null](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ThomTransversality.lean)
-/
@[path]
omit [CompactSpace M] in
proof of Sard's theorem). -/
private theorem sard_critical_values_null
  (n : ℕ)
  (f : M → EuclideanSpace ℝ (Fin n))
  (hf : ContMDiff I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) f) :
  MeasureTheory.volume
    (f '' {x | ¬ Function.Surjective (mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) f x)}) = 0 := by
  have h := _root_.MathlibExt.Geometry.Manifold.SardWanted.sard_theorem f hf
  unfold _root_.MathlibExt.Geometry.Manifold.SardWanted.criticalValues
    _root_.MathlibExt.Geometry.Manifold.SardWanted.criticalSet at h
  exact h

end MathlibExt.Geometry.Manifold.ThomTransversalityWanted

namespace MathlibExt.Geometry.Manifold.ThomTransversalityWanted

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M] [CompactSpace M] [SecondCountableTopology M]
/--
[exists_small_regular_value](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ThomTransversality.lean)
-/
@[path]
omit [CompactSpace M] in
derivatives. -/
private lemma exists_small_regular_value
  (n : ℕ)
  (f : M → EuclideanSpace ℝ (Fin n))
  (hf : ContMDiff I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ c : EuclideanSpace ℝ (Fin n), ‖c‖ < ε ∧
    ∀ x : M, f x = c →
      Function.Surjective (mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) f x) := by
  have hS := sard_critical_values_null n f hf
  have hball : ¬ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε ⊆
    f '' {x | ¬ Function.Surjective (mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) f x)} := by
    intro hsub
    have hnull := MeasureTheory.measure_mono_null hsub hS
    have hpos := Metric.measure_ball_pos MeasureTheory.volume
      (0 : EuclideanSpace ℝ (Fin n)) hε
    rw [hnull] at hpos
    exact lt_irrefl 0 hpos
  rw [Set.not_subset] at hball
  obtain ⟨c, hcball, hcS⟩ := hball
  refine ⟨c, mem_ball_zero_iff.mp hcball, ?_⟩
  intro x hx
  by_contra hns
  apply hcS
  rw [← hx]
  exact Set.mem_image_of_mem f hns
omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I (⊤ : ℕ∞) M]
  [T2Space M] [CompactSpace M] [SecondCountableTopology M] in

end MathlibExt.Geometry.Manifold.ThomTransversalityWanted

namespace MathlibExt.Geometry.Manifold.ThomTransversalityWanted

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M] [CompactSpace M] [SecondCountableTopology M]
/--
[mfderiv_sub_const_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ThomTransversality.lean)
-/
@[path]
private lemma mfderiv_sub_const_eq
  (n : ℕ)
  (f : M → EuclideanSpace ℝ (Fin n))
  (hf : ContMDiff I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) f)
  (c : EuclideanSpace ℝ (Fin n))
  (x : M) :
  mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (fun y => f y - c) x =
    mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) f x := by
  have hdiff : MDifferentiableAt I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) f x :=
    hf.mdifferentiableAt (by simp)
  have h1 := hdiff.hasMFDerivAt
  have h2 : HasMFDerivAt I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (fun _ => c) x 0 :=
    hasMFDerivAt_const c x
  have hsub := h1.sub h2
  have heq := hsub.mfderiv
  exact heq.trans (sub_zero _)

end MathlibExt.Geometry.Manifold.ThomTransversalityWanted

namespace MathlibExt.Geometry.Manifold.ThomTransversalityWanted

/--
[thom_transversality_uniform_approx_regular_value_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ThomTransversality.lean)
-/
@[path]
lemma thom_transversality_uniform_approx_regular_value_zero
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M] [SecondCountableTopology M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I (⊤ : ℕ∞) M]
  {n : ℕ}
  {f : M → EuclideanSpace ℝ (Fin n)}
  {ε : ℝ}
-- given
  (hf : ContMDiff I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) f)
  (hε : 0 < ε) :
-- imply
  ∃ (g : M → EuclideanSpace ℝ (Fin n)),
    ContMDiff I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) g ∧
    (∀ x : M, ‖f x - g x‖ < ε) ∧
    (∀ x : M, g x = 0 →
    Function.Surjective (mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) g x)) := by
-- proof
  obtain ⟨c, hc_norm, hc_reg⟩ := exists_small_regular_value n f hf ε hε
  refine ⟨fun x => f x - c, hf.sub contMDiff_const, ?_, ?_⟩
  · intro x
    have h : f x - (f x - c) = c := sub_sub_cancel _ _
    rwa [h]
  · intro x hx
    have hfc : f x = c := sub_eq_zero.mp hx
    have hsurj := hc_reg x hfc
    have heq := mfderiv_sub_const_eq n f hf c x
    rwa [heq]

end MathlibExt.Geometry.Manifold.ThomTransversalityWanted

namespace MathlibExt.Geometry.Manifold.ThomTransversalityWanted

/--
[thom_transversality_compact_source_uniform_approx_regular_value_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ThomTransversality.lean)
-/
@[path]
lemma thom_transversality_compact_source_uniform_approx_regular_value_zero
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M] [SecondCountableTopology M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I (⊤ : ℕ∞) M]
  {n : ℕ}
  {f : M → EuclideanSpace ℝ (Fin n)}
  {ε : ℝ}
-- given
  (hf : ContMDiff I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) f)
  (hε : 0 < ε) :
-- imply
  ∃ (g : M → EuclideanSpace ℝ (Fin n)),
    ContMDiff I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) g ∧
    (∀ x : M, ‖f x - g x‖ < ε) ∧
    (∀ x : M, g x = 0 →
    Function.Surjective (mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) g x)) := by
-- proof
  exact thom_transversality_uniform_approx_regular_value_zero f hf ε hε
end MathlibExt.Geometry.Manifold.ThomTransversalityWanted



-- created on 2026-10-20
-- updated on 2026-10-23
