/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean -/

import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# The Dickman–de Bruijn function

This file defines a reusable predicate characterizing the Dickman–de Bruijn function on `ℝ`.
It records the standard zero extension to negative inputs, its range and continuity on
nonnegative inputs, its normalization on `[0, 1]`, and its delay differential equation above
one. Existence and uniqueness are proved separately in
`MathlibExt.Analysis.SpecialFunctions.DickmanDeBruijnExistsUnique`.

## References

* [Ofir Gorodetsky, *Rigidity of Averages over the Two Largest Prime
  Factors*](https://arxiv.org/abs/2608.05191)
* [Jared Duker Lichtman, *An improvement on the largest prime factors of consecutive
  integers*](https://arxiv.org/abs/2607.16032)
-/

namespace Real

/-- `IsDickmanDeBruijn ρ` says that `ρ` is the Dickman–de Bruijn function, extended by zero to
negative inputs. Continuity is asserted only on the original nonnegative domain, since the total
zero extension is discontinuous at zero. -/
def IsDickmanDeBruijn (ρ : ℝ → ℝ) : Prop :=
  (∀ u, u < 0 → ρ u = 0) ∧
    Set.MapsTo ρ (Set.Ici (0 : ℝ)) (Set.Icc (0 : ℝ) 1) ∧
    ContinuousOn ρ (Set.Ici (0 : ℝ)) ∧
    (∀ u ∈ Set.Icc (0 : ℝ) 1, ρ u = 1) ∧
    ∀ u, 1 < u → DifferentiableAt ℝ ρ u ∧ u * deriv ρ u + ρ (u - 1) = 0
end Real
