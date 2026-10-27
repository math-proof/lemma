/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/CubicSurface.lean -/


import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Def.AlgebraicGeometry.CubicSurface.Part2


namespace AlgebraicGeometry

open MvPolynomial in
/-- The triple hyperplane is not smooth: `[0 : 1 : 0 : 0]` is a singular point (checked over
the algebraic closure, where smoothness is defined). -/
example (k : Type*) [Field k] : ¬ (triplePlane (k := AlgebraicClosure k)).IsSmooth := by
  intro h
  have hsing : (triplePlane (k := AlgebraicClosure k)).IsSingularPoint ![0, 1, 0, 0] := by
    refine ⟨by simp [triplePlane], fun i => ?_⟩
    fin_cases i <;> simp [triplePlane, pderiv_X]
  have hx := congrFun (h _ hsing) 1
  simp at hx

end AlgebraicGeometry
