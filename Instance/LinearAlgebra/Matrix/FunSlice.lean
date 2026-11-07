import Def.LinearAlgebra.Matrix.FunSlice


/-- Unit-step slice `V[start:stop]` of `ℕ ⇀ Fin d ⇀ ℝ` as a real matrix.
Each entry stays in `ℝ`, so this coercion is computable. -/
instance {d : ℕ} {start stop : ℤ} :
    Coe (FunSlice.Out (Fun (Fin d) ℝ) ⟨start, stop, (1 : ℤ)⟩)
      (Matrix (Fin (stop.toNat - start.toNat)) (Fin d) ℝ) where
  coe := Matrix.ofFunSlice

/-- Prefix slice `V[:n]` of `ℕ ⇀ Fin d ⇀ ℝ` as a real matrix.
Each entry stays in `ℝ`, so this coercion is computable. -/
instance {n d : ℕ} :
    Coe (FunSlice.Out (Fun (Fin d) ℝ) ⟨(0 : ℤ), (n : ℤ), (1 : ℤ)⟩)
      (Matrix (Fin n) (Fin d) ℝ) where
  coe := Matrix.ofFunSlicePrefix
