/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Hurwitz.lean -/

import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.OpenMapping
open Filter Metric Set
open scoped Topology

variable {α : Type*} {F : α → ℂ → ℂ} {f : ℂ → ℂ}
  {φ : Filter α} {U : Set ℂ}
/-!
# Hurwitz theorem: zero-free dichotomy for locally uniform limits (N327)

Let `F : α → ℂ → ℂ` converge locally uniformly on an open preconnected
set `U` to `f`, with each `F n` eventually holomorphic and zero-free on
`U`. Then either `f` vanishes identically on `U` or `f` is zero-free on
`U`. The witness corollary upgrades a single nonzero value of `f` inside
`U` to global zero-freeness on `U`.

The proof is Hurwitz's theorem. The limit is holomorphic by Mathlib's
locally uniform limit theorem. If `f` is neither identically zero nor
zero-free, pick a zero `z₀` and a point where `f` is nonzero; the
isolated-zero principle gives a closed ball around `z₀` inside `U` with
`f` nonzero on the punctured ball. The norm of `f` attains a positive
minimum `m` on the sphere. One approximant is uniformly within `m / 4`
of `f` on the closed ball, so it stays at distance at least `m / 2`
from its center value on the sphere. If the approximant is nonconstant
near `z₀`, `DiffContOnCl.ball_subset_image_closedBall` forces `0` into
its image, against zero-freeness; if it is locally constant, the
identity principle makes it globally constant and the triangle
inequality at the minimum point gives a contradiction.
-/


