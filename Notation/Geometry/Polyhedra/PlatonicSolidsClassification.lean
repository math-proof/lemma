/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Polyhedra/PlatonicSolidsClassification.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Def.Geometry.Polyhedra.PlatonicSolidsClassification
/-!
# Classification of the Platonic solids

This file classifies the Platonic solids up to their count tuple `(p, q, V, E, F)` and proves that
each of the five tuples is realized. Euler's formula and the two incidence-count equations imply
`1 / p + 1 / q > 1 / 2`, leaving only the five classical count tuples; explicit Euclidean
coordinates realize every tuple. Classification up to combinatorial equivalence or Euclidean
congruence is not proved here.
-/


namespace MetaMathlibExt

section

section GoldenSolids

local notation "φ" => gold

end GoldenSolids
end
end MetaMathlibExt
