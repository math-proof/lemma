import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.Buildings.code.Building.TitsTheoremAssembly
open AptIsCoxeterProof ChamberComplex


/--
[tits_theorem_hyp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/TitsTheoremAssembly.lean)
-/
@[path]
private lemma tits_theorem_hyp_eq
  [DecidableEq V] :
-- imply
  TitsTheoremHyp V := by
-- proof
  apply tits_theorem_hyp


-- created on 2026-10-23
