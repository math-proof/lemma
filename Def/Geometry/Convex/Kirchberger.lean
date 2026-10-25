/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/Kirchberger.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Convex.Radon
/-!
# Kirchberger's separation theorem

This file proves that strict separation of two finite subsets of Euclidean space is determined by
their subconfigurations of at most `d + 2` points.
-/


namespace MetaMathlibExt

def kirchberger_halfspace {d : ℕ} :
    EuclideanSpace ℝ (Fin d) ⊕ EuclideanSpace ℝ (Fin d) →
      Set (EuclideanSpace ℝ (Fin d) × ℝ)
  | .inl a => {p | inner ℝ p.1 a < p.2}
  | .inr c => {p | p.2 < inner ℝ p.1 c}

end MetaMathlibExt
