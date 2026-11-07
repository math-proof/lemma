/-- Parameter-indexed map: `f[i]` is the index; juxta after is a normal call on the residual.
For time-indexed trajectories `r : Fun ℕ (Ω → α)`, also `r[t:]` via `Fun.getSliceFrom`
and closed slices `r[:n]` / `r[a:b]` via `Fun.getSlice` (see `Def.Probability.Process.HiddenMarkovSequence.Part2`). -/
structure Fun (ι : Type _) (α : Type _) where
  toFun : ι → α

/-- Dependent indexed map, written `(i : ι) ⇀ α i`. -/
structure PiFun {ι : Type _} (α : ι → Type _) where
  toFun : (i : ι) → α i

instance {ι : Type _} {α : ι → Type _} : CoeFun (PiFun α) (fun _ => (i : ι) → α i) where
  coe := PiFun.toFun
