import Mathlib.Data.Matrix.Basic
import Notation.Fun
import Syntax.Data.List


/-- Unit-step slice of `ℕ ⇀ Fin d ⇀ ℝ` as a real matrix.
Rows are `Fin (stop.toNat - start.toNat)`. -/
def Matrix.ofFunSlice {d : ℕ} {start stop : ℤ}
    (s : FunSlice.Out (Fun (Fin d) ℝ) ⟨start, stop, (1 : ℤ)⟩) :
    Matrix (Fin (stop.toNat - start.toNat)) (Fin d) ℝ :=
  Matrix.of fun i a =>
    let rows : Fin (stop.toNat - start.toNat) → Fun (Fin d) ℝ := s
    (rows i).toFun a

/-- Prefix slice of `ℕ ⇀ Fin d ⇀ ℝ` as a real matrix. -/
def Matrix.ofFunSlicePrefix {n d : ℕ}
    (s : FunSlice.Out (Fun (Fin d) ℝ) ⟨(0 : ℤ), (n : ℤ), (1 : ℤ)⟩) :
    Matrix (Fin n) (Fin d) ℝ :=
  Matrix.of fun i a =>
    let rows : Fin ((n : ℤ).toNat - (0 : ℤ).toNat) → Fun (Fin d) ℝ := s
    (rows ⟨(i : ℕ), by
      have h : (n : ℤ).toNat = n := Int.toNat_natCast n
      simp [h]⟩).toFun a

/-- Length of the singleton integer slice `n:n+1`. -/
theorem Matrix.funSlice_singleton_length (n : ℕ) :
    ((n : ℤ) + 1).toNat - (n : ℤ).toNat = 1 := by
  have h0 : (n : ℤ).toNat = n := Int.toNat_natCast n
  have h1 : ((n : ℤ) + 1).toNat = n + 1 := by
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) from (by norm_cast)]
    exact Int.toNat_natCast (n + 1)
  omega

/-- Singleton slice `V[n:n+1]` as a 1-row real matrix.
Used by the `CoeDep` instance; prefer the cast `(s : ℝ ^ [1, d])` at call sites. -/
def Matrix.ofFunSliceSingleton {d n : ℕ}
    (s : FunSlice.Out (Fun (Fin d) ℝ) ⟨(n : ℤ), (n : ℤ) + 1, (1 : ℤ)⟩) :
    Matrix (Fin 1) (Fin d) ℝ :=
  Matrix.of fun i a =>
    let rows : Fin (((n : ℤ) + 1).toNat - (n : ℤ).toNat) → Fun (Fin d) ℝ := s
    (rows ⟨(i : ℕ), by
      have h := Matrix.funSlice_singleton_length n
      omega⟩).toFun a
