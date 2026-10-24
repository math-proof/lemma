import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.SWModuliGoal62


/--
[SWGaugeEquivalent.refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SWModuliGoal62.lean)
-/
@[path]
lemma SWGaugeEquivalent.refl
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  {gauge : GaugeActionData spinc}
  {sol : SWSolution spinc} :
-- imply
  SWGaugeEquivalent gauge sol sol :=
-- proof
  ⟨1, gauge.gauge_action_one sol⟩

/--
[sw_moduli_dimension_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SWModuliGoal62.lean)
-/
@[path]
lemma sw_moduli_dimension_formula
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ⊤ M]
  [CompactSpace M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  [htop : Has4ManifoldTopology M]
  {spinc : SpinCStructure M Ω1 Ω2}
  [hgeneric : IsGenericPair spinc]
  {sm : SWModuliSmoothManifold spinc}
  {sol : SWSolution spinc}
-- given
  (hdim_eq_index : ∀ (sol : SWSolution spinc), (sm.dimension : ℤ) = hgeneric.fredholmIndex sol) :
-- imply
  (sm.dimension : ℤ) * 4 = spinc.c₁_L - (2 * htop.euler + 3 * htop.Q.signature) := by
-- proof
  have hdim : (sm.dimension : ℤ) = hgeneric.fredholmIndex sol := hdim_eq_index sol
  have hindex : hgeneric.fredholmIndex sol * 4 =
    spinc.c₁_L - (2 * htop.euler + 3 * htop.Q.signature) :=
    hgeneric.fredholmIndex_eq sol
  linarith
/-- Theorem 1: for generic $(g, \mu)$, the SW moduli space $\mathcal{M}$ is a smooth, compact, orientable manifold of dimension $d(S) = \tfrac{1}{4}(c_1(L)^2 \cdot [X] - (2\chi + 3\sigma))$. -/


-- created on 2026-10-23
