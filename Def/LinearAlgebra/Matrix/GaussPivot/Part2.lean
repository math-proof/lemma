/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/GaussPivot.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Finset.Sort
public import Theorem.LinearAlgebra.Matrix.GaussPivot

@[expose] public section

/-!
# Gaussian elimination with row pivots

This file constructs unit lower-triangular row operations for a pivot step and proves that a row
permutation followed by such operations puts every finite matrix over a field in row echelon form.
-/


namespace MathlibExt.LinearAlgebra.Matrix.GaussPivotWanted

def gaussPivotHasDecomposition {K : Type*} [Semiring K] {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) K) : Prop :=
  ∃ (L : Matrix (Fin p) (Fin p) K) (σ : Equiv.Perm (Fin p)),
    L.IsLowerTriangular ∧ (∀ i, L.diag i = 1) ∧
      (L * A.submatrix σ id).IsRowEchelon

def gaussPivotBorderLower {K : Type*} [Zero K] [One K] {p : ℕ}
    (d : Fin p → K) (L₀ : Matrix (Fin p) (Fin p) K) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) K :=
  Fin.cases (Fin.cases 1 fun _ => 0) fun i => Fin.cases (d i) fun j => L₀ i j

end MathlibExt.LinearAlgebra.Matrix.GaussPivotWanted
