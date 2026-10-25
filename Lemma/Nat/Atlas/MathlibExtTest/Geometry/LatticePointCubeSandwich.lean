import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.Geometry.LatticePointCubeSandwich
open LatticePointCubeSandwich MeasureTheory


/--
[singleton_zero_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/LatticePointCubeSandwich.lean)
-/
@[path]
lemma singleton_zero_bounded
-- imply
  Bornology.IsBounded ({0} : Set (Fin 0 → ℝ)) :=
-- proof
  Bornology.isBounded_singleton

/--
[halfOpenUnit_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/LatticePointCubeSandwich.lean)
-/
@[path]
lemma halfOpenUnit_bounded
-- imply
  Bornology.IsBounded halfOpenUnit :=
-- proof
  Bornology.IsBounded.pi (fun _ => Metric.isBounded_Ico 0 1)


-- created on 2026-10-23
