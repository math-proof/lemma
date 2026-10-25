import Mathlib
import sympy.Basic
import Structure.v1.Atlas.GeometryOfManifolds.code.PontrjaginObstructions.Part7
open scoped Manifold


/--
[HasChernPontrjaginData.chern_pontrjagin_rel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/PontrjaginObstructions.lean)
-/
@[path]
lemma HasChernPontrjaginData.chern_pontrjagin_rel
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (𝓡 4) ⊤ M]
  [CompactSpace M]
  [Mfd4Topology M]
-- given
  (hcp : HasChernPontrjaginData M) :
-- imply
  hcp.c₁_sq = 2 * hcp.c₂ + hcp.p₁ := by
-- proof
  unfold HasChernPontrjaginData.p₁
  ring

/--
[ChernPontrjaginDataClosed.chern_pontrjagin_rel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/PontrjaginObstructions.lean)
-/
@[path]
lemma ChernPontrjaginDataClosed.chern_pontrjagin_rel
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (𝓡 4) ⊤ M]
  [CompactSpace M]
  {data : ChernPontrjaginDataClosed M} :
-- imply
  data.c₁_sq = 2 * data.c₂ + data.mfd.p₁ := by
-- proof
  linarith [data.p₁_whitney]

/--
[not_sum_of_two_squares_14](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/PontrjaginObstructions.lean)
-/
@[path]
lemma not_sum_of_two_squares_14
-- imply
  ∀ a b : ℤ, a ^ 2 + b ^ 2 ≠ 14 := by
-- proof
  intro a b h
  have ha2 : a ^ 2 ≤ 14 := by nlinarith [sq_nonneg b]
  have hb2 : b ^ 2 ≤ 14 := by nlinarith [sq_nonneg a]
  have ha_lo : -4 < a := by nlinarith [sq_nonneg (a + 4)]
  have ha_hi : a < 4 := by nlinarith [sq_nonneg (a - 4)]
  have hb_lo : -4 < b := by nlinarith [sq_nonneg (b + 4)]
  have hb_hi : b < 4 := by nlinarith [sq_nonneg (b - 4)]
  interval_cases a <;> interval_cases b <;> omega
/-- Obstruction example: $\mathbb{CP}^2 \# \mathbb{CP}^2$ (with $b_2 = 2$, $\sigma = 2$,
$\chi = 4$) admits no almost-complex structure, since the Chern number formula forces
$c_1^2 = 14$, which cannot be written as a sum of two squares. -/


-- created on 2026-10-23
