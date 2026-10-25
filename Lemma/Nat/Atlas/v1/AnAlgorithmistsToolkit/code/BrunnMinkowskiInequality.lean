import Mathlib
import sympy.Basic
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.BrunnMinkowskiInequality
open BrunnsTheorem
open MeasureTheory Measure Pointwise
open MeasureTheory Set Pointwise
open scoped ENNReal NNReal


namespace BrunnsTheorem

/--
[slice_minkowski_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/BrunnMinkowskiInequality.lean)
-/
@[path]
lemma slice_minkowski_subset
  {n : ℕ}
  {K : Set (Fin (n + 1) → ℝ)}
  {r t : ℝ}
  {a b : ℝ}
-- given
  (hK : Convex ℝ K)
  (ha : 0 ≤ a)
  (hb : 0 ≤ b)
  (hab : a + b = 1) :
-- imply
  a • (parallelSlice K r) + b • (parallelSlice K t) ⊆ parallelSlice K (a * r + b * t) := by
-- proof
  intro z hz
  obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_add.mp hz
  obtain ⟨x, hx, hux⟩ := Set.mem_smul_set.mp hu
  obtain ⟨y, hy, hvy⟩ := Set.mem_smul_set.mp hv
  show Fin.cons (a * r + b * t) z ∈ K
  have key : a • (Fin.cons r x : Fin (n+1) → ℝ) + b • (Fin.cons t y : Fin (n+1) → ℝ) =
    (Fin.cons (a * r + b * t) (a • x + b • y) : Fin (n+1) → ℝ) := by
    funext i; refine Fin.cases ?_ ?_ i
    · simp [Pi.smul_apply, Pi.add_apply, Fin.cons_zero, smul_eq_mul]
    · intro j; simp [Pi.smul_apply, Pi.add_apply, Fin.cons_succ, smul_eq_mul]
  have hzeq : z = a • x + b • y := by
    rw [← hux, ← hvy] at huv; exact huv.symm
  rw [hzeq, ← key]; exact hK hx hy ha hb hab

end BrunnsTheorem


-- created on 2026-10-23
