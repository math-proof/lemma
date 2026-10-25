import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.Analysis.Convex.LinearProgrammingDuality


namespace LinearProgrammingDualityTest

/--
[oneDimA_mulVec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Convex/LinearProgrammingDuality.lean)
-/
@[path]
private lemma oneDimA_mulVec (x : Fin 1 → ℝ) (j : Fin 1) :
  oneDimA.mulVec x j = x 0 := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  simp [oneDimA, Matrix.mulVec, dotProduct]

end LinearProgrammingDualityTest

namespace LinearProgrammingDualityTest

/--
[oneDimA_transpose_mulVec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Convex/LinearProgrammingDuality.lean)
-/
@[path]
private lemma oneDimA_transpose_mulVec (y : Fin 1 → ℝ) (i : Fin 1) :
  (oneDimA.transpose.mulVec y) i = y 0 := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  unfold oneDimA
  have h11 : (Matrix.transpose (![![1]] : Matrix (Fin 1) (Fin 1) ℝ)) 0 0 = 1 := rfl
  simp [Matrix.mulVec, dotProduct, h11]

end LinearProgrammingDualityTest

namespace LinearProgrammingDualityTest

/--
[oneDim_feas](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Convex/LinearProgrammingDuality.lean)
-/
@[path]
private lemma oneDim_feas :
  ∃ x : Fin 1 → ℝ, (∀ i, 0 ≤ x i) ∧
    ∀ j, oneDimA.mulVec x j ≤ ![5] j := by
  refine ⟨![5], Fin.forall_fin_one.mpr ?_, fun j => ?_⟩
  · simp
  · rw [oneDimA_mulVec]
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp

end LinearProgrammingDualityTest

namespace LinearProgrammingDualityTest

/--
[oneDim_bdd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Convex/LinearProgrammingDuality.lean)
-/
@[path]
private lemma oneDim_bdd (x : Fin 1 → ℝ) (hx : ∀ i, 0 ≤ x i)
  (hAx : ∀ j, oneDimA.mulVec x j ≤ ![5] j) :
  (fun _ => (2 : ℝ)) ⬝ᵥ x ≤ 10 := by
  have h5 : x 0 ≤ 5 := by
    have h := hAx 0
    rw [oneDimA_mulVec] at h
    simpa using h
  have hnn : 0 ≤ x 0 := hx 0
  have hval : (fun _ => (2 : ℝ)) ⬝ᵥ x = 2 * x 0 := by
    simp [dotProduct]
  rw [hval]
  linarith

end LinearProgrammingDualityTest


-- created on 2026-10-23
