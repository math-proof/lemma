import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.OrderAxiom
open CoxeterGroup


namespace Definitions
end Definitions
namespace CoxeterGroup

/--
[sigmaWord_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/OrderAxiom.lean)
-/
@[path]
private lemma sigmaWord_singleton
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B} :
-- imply
  sigmaWord M [s] = sigmaLin M s := by
-- proof
  simp [sigmaWord]

end CoxeterGroup

/--
[sigmaWord_cons](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/OrderAxiom.lean)
-/
@[path]
private lemma sigmaWord_cons_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {w : List B} :
-- imply
  sigmaWord M (s :: w) = sigmaLin M s * sigmaWord M w := by
-- proof
  apply CoxeterGroup.sigmaWord_cons M s w


-- created on 2026-10-24
