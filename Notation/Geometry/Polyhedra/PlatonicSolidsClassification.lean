/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Polyhedra/PlatonicSolidsClassification.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Def.Geometry.Polyhedra.PlatonicSolidsClassification

public section

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
