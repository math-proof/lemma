import Mathlib.Data.Matrix.Basic
import Notation.Fun
import Syntax.Data.List


/-- Prefix slice of `ℕ ⇀ Fin d ⇀ ℝ` as a real matrix. -/
def Matrix.ofFunSlicePrefix {n d : ℕ}
    (s : FunSlice.Out (Fun (Fin d) ℝ) ⟨(0 : ℤ), (n : ℤ), (1 : ℤ)⟩) :
    Matrix (Fin n) (Fin d) ℝ :=
  Matrix.of fun i a =>
    let rows : Fin ((n : ℤ).toNat - (0 : ℤ).toNat) → Fun (Fin d) ℝ := s
    (rows ⟨(i : ℕ), by
      have h : (n : ℤ).toNat = n := Int.toNat_natCast n
      simp [h]⟩).toFun a
