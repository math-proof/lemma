import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.LSeries.RiemannZeta


/--
[meromorphicOn_riemannZeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannZeta.lean)
-/
@[path]
private lemma meromorphicOn_riemannZeta_eq
  :
-- imply
  MeromorphicOn riemannZeta Set.univ := by
-- proof
  apply meromorphicOn_riemannZeta


-- created on 2026-10-20
