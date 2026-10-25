import Mathlib
import sympy.Basic
import Def.Geometry.TwoD
import Lemma.Set.TwoD
open scoped EuclideanSpace


namespace MetaMathlibExt

/--
[varignon](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Varignon.lean)
-/
@[path]
lemma varignon
  :
-- imply
  ∀ (A B C D P Q R S : EuclideanSpace ℝ (Fin 2)),
    2 • P = A + B → 2 • Q = B + C → 2 • R = C + D → 2 • S = D + A →
    P + R = Q + S ∧
    2 * (EuclideanGeometry.orientedTriangleArea P Q R +
    EuclideanGeometry.orientedTriangleArea P R S) =
    EuclideanGeometry.orientedTriangleArea A B C +
    EuclideanGeometry.orientedTriangleArea A C D := by
-- proof
  intro A B C D P Q R S hP hQ hR hS
  have hP0 : 2 * P 0 = A 0 + B 0 := by
    have h := congrArg (fun X => X (0 : Fin 2)) hP
    simpa using h
  have hP1 : 2 * P 1 = A 1 + B 1 := by
    have h := congrArg (fun X => X (1 : Fin 2)) hP
    simpa using h
  have hQ0 : 2 * Q 0 = B 0 + C 0 := by
    have h := congrArg (fun X => X (0 : Fin 2)) hQ
    simpa using h
  have hQ1 : 2 * Q 1 = B 1 + C 1 := by
    have h := congrArg (fun X => X (1 : Fin 2)) hQ
    simpa using h
  have hR0 : 2 * R 0 = C 0 + D 0 := by
    have h := congrArg (fun X => X (0 : Fin 2)) hR
    simpa using h
  have hR1 : 2 * R 1 = C 1 + D 1 := by
    have h := congrArg (fun X => X (1 : Fin 2)) hR
    simpa using h
  have hS0 : 2 * S 0 = D 0 + A 0 := by
    have h := congrArg (fun X => X (0 : Fin 2)) hS
    simpa using h
  have hS1 : 2 * S 1 = D 1 + A 1 := by
    have h := congrArg (fun X => X (1 : Fin 2)) hS
    simpa using h
  have hPR : P + R = Q + S := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp <;> linarith
  refine ⟨hPR, ?_⟩
  simp only [EuclideanGeometry.orientedTriangleArea_eq_det]
  simp [Matrix.det_fin_three]
  have sP0 : P 0 = (A 0 + B 0) / 2 := by linarith
  have sP1 : P 1 = (A 1 + B 1) / 2 := by linarith
  have sQ0 : Q 0 = (B 0 + C 0) / 2 := by linarith
  have sQ1 : Q 1 = (B 1 + C 1) / 2 := by linarith
  have sR0 : R 0 = (C 0 + D 0) / 2 := by linarith
  have sR1 : R 1 = (C 1 + D 1) / 2 := by linarith
  have sS0 : S 0 = (D 0 + A 0) / 2 := by linarith
  have sS1 : S 1 = (D 1 + A 1) / 2 := by linarith
  rw [sP0, sP1, sQ0, sQ1, sR0, sR1, sS0, sS1]
  ring
end



-- created on 2026-10-20
-- updated on 2026-10-23
