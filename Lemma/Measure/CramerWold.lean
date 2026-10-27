import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory
open scoped Topology


namespace MathlibExt.Probability.CramerWoldWanted

/--
[cramer_wold_device](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/CramerWold.lean)
-/
@[path]
lemma cramer_wold_device
  [MeasurableSpace Ω] [MeasurableSpace Ω']
  {d : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {X : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
  {Z : Ω' → EuclideanSpace ℝ (Fin d)}
-- given
  (h : ∀ t : EuclideanSpace ℝ (Fin d), TendstoInDistribution (fun n (ω : Ω) => @inner ℝ (EuclideanSpace ℝ (Fin d)) _ t (X n ω)) Filter.atTop (fun ω' => @inner ℝ (EuclideanSpace ℝ (Fin d)) _ t (Z ω')) (fun _ => μ) μ') :
-- imply
  TendstoInDistribution X Filter.atTop Z (fun _ => μ) μ' := by
-- proof
  have hZ : AEMeasurable Z μ' := by
    have hcoord : ∀ i, AEMeasurable (fun ω' => Z ω' i) μ' := by
      intro i
      have hlim := (h (EuclideanSpace.single i 1)).aemeasurable_limit
      have heq : (fun ω' => Z ω' i)
        = (fun ω' => @inner ℝ (EuclideanSpace ℝ (Fin d)) _
          (EuclideanSpace.single i 1) (Z ω')) := by
        funext ω'
        rw [EuclideanSpace.inner_single_left]
        simp
      rwa [heq]
    have hpi : AEMeasurable (fun x => (Z x).ofLp) μ' :=
      (aemeasurable_pi_iff (δ := Fin d) (X := fun _ => ℝ)).mpr hcoord
    have heq : Z = (WithLp.toLp 2) ∘ (fun x => (Z x).ofLp) := rfl
    rw [heq]
    exact (WithLp.measurable_toLp 2 _).comp_aemeasurable hpi
  have hX : ∀ n, AEMeasurable (X n) μ := by
    intro n
    have hcoord : ∀ i, AEMeasurable (fun ω => (X n ω) i) μ := by
      intro i
      have hni := ((h (EuclideanSpace.single i 1)).forall_aemeasurable n)
      have heq : (fun ω => (X n ω) i)
        = (fun ω => @inner ℝ (EuclideanSpace ℝ (Fin d)) _
          (EuclideanSpace.single i 1) (X n ω)) := by
        funext ω
        rw [EuclideanSpace.inner_single_left]
        simp
      rwa [heq]
    have hpi : AEMeasurable (fun x => ((X n x)).ofLp) μ :=
      (aemeasurable_pi_iff (δ := Fin d) (X := fun _ => ℝ)).mpr hcoord
    have heq : X n = (WithLp.toLp 2) ∘ (fun x => ((X n x)).ofLp) := rfl
    rw [heq]
    exact (WithLp.measurable_toLp 2 _).comp_aemeasurable hpi
  refine TendstoInDistribution.of_inner hZ hX fun t => ?_
  have ht := h t
  refine ht.congr
    (fun n => Filter.Eventually.of_forall (fun ω => real_inner_comm (X n ω) t))
    (Filter.Eventually.of_forall (fun ω' => real_inner_comm (Z ω') t))

end MathlibExt.Probability.CramerWoldWanted


-- created on 2026-10-20
-- updated on 2026-10-26
