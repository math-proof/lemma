import Def.LinearAlgebra.Matrix.FunSlice


/-- Unit-step slice `V[start:stop]` of `ℕ ⇀ Fin d ⇀ ℝ` as a real matrix.
Each entry stays in `ℝ`, so this coercion is computable. -/
instance {d : ℕ} {start stop : ℤ} :
    Coe (FunSlice.Out ((Fin d) ⇀ ℝ) ⟨start, stop, (1 : ℤ)⟩)
      (Matrix (Fin (stop.toNat - start.toNat)) (Fin d) ℝ) where
  coe := Matrix.ofFunSlice

/-- Prefix slice `V[:n]` of `ℕ ⇀ Fin d ⇀ ℝ` as a real matrix.
Each entry stays in `ℝ`, so this coercion is computable. -/
instance {n d : ℕ} :
    Coe (FunSlice.Out ((Fin d) ⇀ ℝ) ⟨(0 : ℤ), (n : ℤ), (1 : ℤ)⟩)
      (Matrix (Fin n) (Fin d) ℝ) where
  coe := Matrix.ofFunSlicePrefix

/-- Prefer the cast `(V[n:n+1] : ℝ ^ [1, d])` for a singleton slice.
`CoeOut` (not plain `Coe`) so `n` need not appear in the target `Fin 1`;
body casts `ofFunSlice` along `funSlice_singleton_length` (no call-site wrapper). -/
instance (priority := high) {d n : ℕ} :
    CoeOut (FunSlice.Out ((Fin d) ⇀ ℝ) ⟨(n : ℤ), (n : ℤ) + 1, (1 : ℤ)⟩)
      (Matrix (Fin 1) (Fin d) ℝ) where
  coe s := (Matrix.funSlice_singleton_length n) ▸ Matrix.ofFunSlice s
