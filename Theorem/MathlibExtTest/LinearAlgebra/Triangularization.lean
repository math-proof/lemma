/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Triangularization.lean -/


import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Trace
import Lemma.Matrix.Triangularization
open scoped BigOperators

open MathlibExt.LinearAlgebra.TriangularizationWanted


-- Triangular similarity over an algebraically closed field exposes determinant and trace.
example {K n : Type*} [Field K] [IsAlgClosed K]
    [Fintype n] [DecidableEq n] [LinearOrder n] (A : Matrix n n K) :
    ∃ P T : Matrix n n K,
      IsUnit P ∧ T.IsUpperTriangular ∧ A = P * T * P⁻¹ ∧
        A.det = ∏ i, T i i ∧ A.trace = ∑ i, T i i := by
  obtain ⟨P, T, hP, hT, hA⟩ :=
    exists_upperTriangular_similar_of_splits A (IsAlgClosed.splits _)
  refine ⟨P, T, hP, hT, hA, ?_, ?_⟩
  · calc
      A.det = (P * T * P⁻¹).det := congrArg Matrix.det hA
      _ = T.det := Matrix.det_conj hP T
      _ = ∏ i, T i i := Matrix.det_of_isUpperTriangular hT
  · have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
    calc
      A.trace = (P * T * P⁻¹).trace := congrArg Matrix.trace hA
      _ = (P⁻¹ * (P * T)).trace := Matrix.trace_mul_comm (P * T) P⁻¹
      _ = ((P⁻¹ * P) * T).trace := by rw [Matrix.mul_assoc]
      _ = T.trace := by rw [Matrix.nonsing_inv_mul P hPdet, one_mul]
      _ = ∑ i, T i i := rfl

-- A triangularizing basis computes the determinant from the matrix diagonal.
example {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (f : Module.End K V) (h : f.charpoly.Splits)
    (hdim : Module.finrank K V = Fintype.card ι) :
    ∃ b : Module.Basis ι K V,
      LinearMap.det f = ∏ i, LinearMap.toMatrix b b f i i := by
  obtain ⟨b, hb⟩ := exists_basis_upperTriangular_toMatrix f h hdim
  refine ⟨b, ?_⟩
  rw [← LinearMap.det_toMatrix b f]
  exact Matrix.det_of_isUpperTriangular hb

