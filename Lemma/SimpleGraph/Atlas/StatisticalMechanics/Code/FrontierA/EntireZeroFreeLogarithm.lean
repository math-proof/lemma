import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.EntireZeroFreeLogarithm
open Set StatMech StatMech.FrontierA


/--
[exists_entireLogarithm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/EntireZeroFreeLogarithm.lean)
-/
@[path]
private lemma exists_entireLogarithm_eq
-- given
  (f : Complex -> Complex)
  (hf : Differentiable Complex f)
  (hzero : forall z, f z ≠ 0) :
-- imply
  exists g : Complex -> Complex, Differentiable Complex g /\ (forall z, Complex.exp (g z) = f z) := by
-- proof
  apply StatMech.FrontierA.exists_entireLogarithm f hf hzero


-- created on 2026-10-23
