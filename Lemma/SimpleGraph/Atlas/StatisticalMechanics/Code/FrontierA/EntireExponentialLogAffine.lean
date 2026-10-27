import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.EntireExponentialLogAffine
open Set Bornology StatMech StatMech.FrontierA


/--
[exists_affine_of_entire_exp_growth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/EntireExponentialLogAffine.lean)
-/
@[path]
private lemma exists_affine_of_entire_exp_growth_eq
  {A B : Real}
-- given
  (g : Complex -> Complex)
  (hg : Differentiable Complex g)
  (hA : 0 < A)
  (hB : 0 <= B)
  (hgrowth : forall z, ‖Complex.exp (g z)‖ <= A * Real.exp (B * ‖z‖)) :
-- imply
  exists a b : Complex, forall z, g z = a * z + b := by
-- proof
  apply StatMech.FrontierA.exists_affine_of_entire_exp_growth g hg A B hA hB hgrowth


-- created on 2026-10-23
