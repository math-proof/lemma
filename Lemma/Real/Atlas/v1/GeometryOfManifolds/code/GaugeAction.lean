import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.GaugeAction.Part2


/--
[gauge_action_preserves_solutions](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/GaugeAction.lean)
-/
@[path]
lemma gauge_action_preserves_solutions
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {ga : @ConcreteGaugeActionData M _ _ Ω1 Ω2 _ _ _ _}
  {f : SWGaugeGroup M}
  {A : ga.Connection}
  {ψ : ga.SpinorSection}
-- given
  (hsol : ga.IsSWSolution A ψ) :
-- imply
  ga.IsSWSolution (ga.gaugeAction f (A, ψ)).1 (ga.gaugeAction f (A, ψ)).2 := by
-- proof
  obtain ⟨hDirac, hCurv⟩ := hsol
  refine ⟨?_, ?_⟩
  ·
    show ga.DiracOp (ga.gaugeAction f (A, ψ)).1 (ga.gaugeAction f (A, ψ)).2 = 0
    simp only [ConcreteGaugeActionData.gaugeAction, ConcreteGaugeActionData.gaugeOnConnection]
    rw [ga.DiracOp_gauge_equivariant, hDirac, ga.gaugeOnNegSpinor_zero]
  ·
    show ∀ φ, ga.cliffordMap (ga.selfDualCurvature (ga.gaugeAction f (A, ψ)).1) φ =
      ga.tracelessQuadratic (ga.gaugeAction f (A, ψ)).2 φ -
        ga.cliffordMap ga.perturbation φ
    simp only [ConcreteGaugeActionData.gaugeAction, ConcreteGaugeActionData.gaugeOnConnection]
    intro φ
    rw [ga.selfDualCurvature_gauge_invariant, ga.tracelessQuadratic_gauge_invariant]
    exact hCurv φ


-- created on 2026-10-23
