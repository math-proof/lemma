module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.v1.Atlas.Buildings.code.Building.TitsTheoremAssembly
open AptIsCoxeterProof ChamberComplex


public section

/--
[tits_theorem_hyp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/TitsTheoremAssembly.lean)
-/
@[path]
private theorem tits_theorem_hyp_eq
  [DecidableEq V] :
-- imply
  TitsTheoremHyp V := by
-- proof
  apply tits_theorem_hyp


-- created on 2026-10-23
