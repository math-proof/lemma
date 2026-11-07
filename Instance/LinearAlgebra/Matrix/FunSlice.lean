import Def.LinearAlgebra.Matrix.FunSlice


/-- Prefix slice `V[:n]` of `ℕ ⇀ Fin d ⇀ ℝ` as a real matrix.
Each entry stays in `ℝ`, so this coercion is computable. -/
instance {n d : ℕ} :
    Coe (FunSlice.Out (Fun (Fin d) ℝ) ⟨(0 : ℤ), (n : ℤ), (1 : ℤ)⟩)
      (Matrix (Fin n) (Fin d) ℝ) where
  coe := Matrix.ofFunSlicePrefix
