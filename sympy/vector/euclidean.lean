import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean coordinate vectors

`EuclideanVec d` is `ℝ^d` with the Euclidean (L²) inner product and norm, i.e. Mathlib's
`EuclideanSpace ℝ (Fin d)`. Ported from rl-theory-in-lean `RLTheory.E d` (renamed so that it does not
clash with the ubiquitous auto-bound type variable `E`).

There is deliberately no coercion `(Fin d → ℝ) → EuclideanVec d`: since `EuclideanSpace` is a
`WithLp` structure, convert explicitly with `WithLp.toLp 2 x` (and back with `WithLp.ofLp v` or `v i`).
-/

-- ℝ^d with the Euclidean inner product (rl: `RLTheory.E d`)
abbrev EuclideanVec (d : ℕ) := EuclideanSpace ℝ (Fin d)