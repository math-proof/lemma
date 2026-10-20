import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ModularForms.JacobiTheta.RamanujanSummability
open scoped Topology
open MetaMathlibExt


/--
[ramanujanTheta_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/RamanujanSummability.lean)
-/
@[path]
private lemma ramanujanTheta_summable_eq
  {a b : ℂ}
-- given
  (h : ‖a * b‖ < 1) :
-- imply
  Summable (fun n : ℤ => ‖ramanujanThetaTerm a b n‖) := by
-- proof
  apply MetaMathlibExt.ramanujanTheta_summable a b h


-- created on 2026-10-20
