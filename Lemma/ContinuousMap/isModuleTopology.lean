import Mathlib
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [TopologicalSpace R]
  [Add S]
  [SMul R S] :
-- imply
  @IsModuleTopology R _ S _ _ (moduleTopology R S) := by
-- proof
  apply inferInstance


-- created on 2026-11-13
