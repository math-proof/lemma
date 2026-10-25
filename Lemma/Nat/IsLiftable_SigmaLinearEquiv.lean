import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.CoxeterHomomorphism.Part2
open Finset BigOperators CoxeterGroup


namespace Definitions
end Definitions
/--
[sigmaLinearEquiv_isLiftable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/CoxeterHomomorphism.lean)
-/
@[path]
private lemma sigmaLinearEquiv_isLiftable_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  M.IsLiftable (fun s => sigmaLinearEquiv M s) := by
-- proof
  apply CoxeterGroup.sigmaLinearEquiv_isLiftable M

/--
[coxeterRepresentation_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/CoxeterHomomorphism.lean)
-/
@[path]
private lemma coxeterRepresentation_simple_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  [Group W]
  {cs : CoxeterSystem M W}
  {s : B} :
-- imply
  coxeterRepresentation M cs (cs.simple s) = sigmaLinearEquiv M s := by
-- proof
  apply CoxeterGroup.coxeterRepresentation_simple M cs s

/--
[coxeterRepresentation_wordProd_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/CoxeterHomomorphism.lean)
-/
@[path]
private lemma coxeterRepresentation_wordProd_apply_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  [Group W]
  {cs : CoxeterSystem M W}
  {word : List B}
  {v : B → ℝ} :
-- imply
  (coxeterRepresentation M cs (cs.wordProd word)) v = wordSigma M word v := by
-- proof
  apply CoxeterGroup.coxeterRepresentation_wordProd_apply M cs word v


-- created on 2026-10-24
