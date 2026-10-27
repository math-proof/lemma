import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[roth_equivMapDomain_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  [Zero M]
  (e : A ≃ B)
  (d : Finsupp B M) :
-- imply
  Finsupp.equivMapDomain e (Finsupp.equivMapDomain e.symm d) = d := by
-- proof
  ext b
  simp [Finsupp.equivMapDomain_apply]


-- created on 2026-10-21
