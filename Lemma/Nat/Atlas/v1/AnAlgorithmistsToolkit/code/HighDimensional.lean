import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.HighDimensional.Part2
open MeasureTheory ProbabilityTheory Finset HighDimensional
open scoped NNReal
open ProbabilityTheory Finset
open scoped ENNReal NNReal
open scoped InnerProductSpace
open Finset


namespace HighDimensional

/--
[projFirstK_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HighDimensional.lean)
-/
@[path]
lemma projFirstK_lipschitz
  {n k : ℕ}
  {x y : EuclideanSpace ℝ (Fin n)}
-- given
  (hk : k ≤ n) :
-- imply
  ‖projFirstK n k hk x - projFirstK n k hk y‖ ≤ ‖x - y‖ := by
-- proof
  simp only [EuclideanSpace.norm_eq, projFirstK]
  apply Real.sqrt_le_sqrt
  have hLHS : ∀ i : Fin k,
    (((WithLp.equiv 2 (Fin k → ℝ)).symm fun j => x (Fin.castLE hk j)) -
      (WithLp.equiv 2 (Fin k → ℝ)).symm fun j => y (Fin.castLE hk j)).ofLp i =
    x (Fin.castLE hk i) - y (Fin.castLE hk i) := by
    intro i; simp [WithLp.equiv, PiLp.sub_apply]
  have hRHS : ∀ j : Fin n, (x - y).ofLp j = x j - y j := by
    intro j; simp [PiLp.sub_apply]
  simp_rw [hLHS, hRHS]
  have h1 : ∑ i : Fin k, ‖x (Fin.castLE hk i) - y (Fin.castLE hk i)‖ ^ 2 =
    ∑ j ∈ Finset.univ.map (Fin.castLEEmb hk), ‖x j - y j‖ ^ 2 := by
    rw [Finset.sum_map]; simp [Fin.castLEEmb]
  rw [h1]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.subset_univ _
  · intro i _ _; positivity

end HighDimensional

namespace HighDimensional

/--
[sphereProjNorm_lipschitzWith](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HighDimensional.lean)
-/
@[path]
lemma sphereProjNorm_lipschitzWith
  {n k : ℕ}
-- given
  (hk : k ≤ n) :
-- imply
  LipschitzWith 1 (sphereProjNorm n k hk) := by
-- proof
  apply LipschitzWith.mk_one
  intro x y
  simp only [sphereProjNorm, normProjFirstK]
  rw [Real.dist_eq]
  calc |‖projFirstK n k hk ↑x‖ - ‖projFirstK n k hk ↑y‖|
    ≤ ‖projFirstK n k hk ↑x - projFirstK n k hk ↑y‖ := abs_norm_sub_norm_le _ _
    _ ≤ ‖(↑x : EuclideanSpace ℝ (Fin n)) - ↑y‖ := projFirstK_lipschitz n k hk ↑x ↑y
    _ = dist x y := by rw [Subtype.dist_eq, dist_eq_norm]

end HighDimensional

namespace HighDimensional

/--
[cthickening_sublevel_of_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HighDimensional.lean)
-/
@[path]
lemma cthickening_sublevel_of_lipschitz
  [PseudoMetricSpace α]
  {f : α → ℝ}
  {M ε : ℝ}
-- given
  (hf : LipschitzWith 1 f)
  (hε : 0 ≤ ε)
  (hne : {x | f x ≤ M}.Nonempty) :
-- imply
  Metric.cthickening ε {x | f x ≤ M} ⊆ {x | f x ≤ M + ε} := by
-- proof
  intro y hy
  simp only [Set.mem_setOf_eq]
  have hinfDist : Metric.infDist y {x | f x ≤ M} ≤ ε := by
    rw [Metric.mem_cthickening_iff] at hy
    have h1 : Metric.infEDist y {x | f x ≤ M} ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy
    calc Metric.infDist y {x | f x ≤ M}
      = (Metric.infEDist y {x | f x ≤ M}).toReal := rfl
      _ ≤ (ENNReal.ofReal ε).toReal :=
        (ENNReal.toReal_le_toReal h1 ENNReal.ofReal_ne_top).mpr hy
      _ = ε := ENNReal.toReal_ofReal hε
  have hbound : f y ≤ M + Metric.infDist y {x | f x ≤ M} := by
    have hNonempty : Nonempty ↥{x | f x ≤ M} := hne.to_subtype
    rw [Metric.infDist_eq_iInf]
    suffices h : ∀ a : ↥{x | f x ≤ M}, f y - M ≤ dist y (a : α) by
      linarith [le_ciInf h]
    intro ⟨a, ha⟩
    simp only [Set.mem_setOf_eq] at ha
    have hLip : dist (f y) (f a) ≤ dist y a := by
      have := hf.dist_le_mul y a; simp at this; exact this
    linarith [show f y - f a ≤ dist y a from
      (le_abs_self _).trans ((Real.dist_eq _ _).symm ▸ hLip)]
  linarith

end HighDimensional

namespace HighDimensional

/--
[cthickening_superlevel_of_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HighDimensional.lean)
-/
@[path]
lemma cthickening_superlevel_of_lipschitz
  [PseudoMetricSpace α]
  {f : α → ℝ}
  {M ε : ℝ}
-- given
  (hf : LipschitzWith 1 f)
  (hε : 0 ≤ ε)
  (hne : {x | f x ≥ M}.Nonempty) :
-- imply
  Metric.cthickening ε {x | f x ≥ M} ⊆ {x | f x ≥ M - ε} := by
-- proof
  intro y hy
  simp only [Set.mem_setOf_eq]
  have hinfDist : Metric.infDist y {x | f x ≥ M} ≤ ε := by
    rw [Metric.mem_cthickening_iff] at hy
    have h1 : Metric.infEDist y {x | f x ≥ M} ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy
    calc Metric.infDist y {x | f x ≥ M}
      = (Metric.infEDist y {x | f x ≥ M}).toReal := rfl
      _ ≤ (ENNReal.ofReal ε).toReal :=
        (ENNReal.toReal_le_toReal h1 ENNReal.ofReal_ne_top).mpr hy
      _ = ε := ENNReal.toReal_ofReal hε
  have hbound : f y ≥ M - Metric.infDist y {x | f x ≥ M} := by
    have hNonempty : Nonempty ↥{x | f x ≥ M} := hne.to_subtype
    rw [Metric.infDist_eq_iInf]
    suffices h : ∀ a : ↥{x | f x ≥ M}, M - f y ≤ dist y (a : α) by
      linarith [le_ciInf h]
    intro ⟨a, ha⟩
    simp only [Set.mem_setOf_eq] at ha
    have hLip : dist (f y) (f a) ≤ dist y a := by
      have := hf.dist_le_mul y a; simp at this; exact this
    linarith [show f a - f y ≤ dist y a from
      (show f a - f y ≤ |f y - f a| by linarith [neg_abs_le (f y - f a)]).trans
        ((Real.dist_eq _ _).symm ▸ hLip)]
  linarith
end HighDimensional
open ProbabilityTheory Finset
open scoped ENNReal NNReal
namespace ChernoffHoeffding



-- created on 2026-10-23
