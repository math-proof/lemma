/-- Parameter-indexed map: `f[i]` is the index; juxta after is a normal call on the residual.
For time-indexed trajectories `r : Fun ℕ (Ω → α)`, also `r[t:]` via `Fun.getSliceFrom`
and closed slices `r[:n]` / `r[a:b]` via `Fun.getSlice` (see `sympy.stats.hidden_markov_sequence`). -/
structure Fun (ι : Type _) (α : Type _) where
  toFun : ι → α
