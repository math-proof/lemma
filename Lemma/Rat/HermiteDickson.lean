import Mathlib
import sympy.Basic
import sympy.atlas.FieldTheory.HermiteDickson
open MathlibExt.FieldTheory.HermiteDickson


/--
[hermite_dickson_permutation_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/HermiteDickson.lean)
-/
@[path]
private lemma hermite_dickson_permutation_criterion_eq
  [Field Fq] [Fintype Fq] [DecidableEq Fq]
  {p : ℕ} [CharP Fq p] [Fact p.Prime]
  {f : Polynomial Fq}
-- given
  (hq : 2 ≤ Fintype.card Fq) :
-- imply
  let q := by
-- proof
  apply MathlibExt.FieldTheory.HermiteDickson.hermite_dickson_permutation_criterion hq f


-- created on 2026-10-20
