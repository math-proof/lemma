import Mathlib
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Add M]
  [SMul R M]
  [TopologicalSpace R]
  [TopologicalSpace M] :
-- imply
  IsModuleTopology R M ↔ ‹TopologicalSpace M› = moduleTopology R M := by
-- proof
  apply Iff.intro
  ·
    intro m
    apply m.eq_moduleTopology'
  ·
    intro a
    apply IsModuleTopology.mk
    apply a


-- created on 2026-11-13
