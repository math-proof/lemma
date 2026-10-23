import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Lemma.Definitions.Def_AlgebraicCurve_Repartitions
import Lemma.Definitions.Def_AlgebraicCurve_AdelicIndex
import Lemma.P2M.Util

open WithZero
open AlgebraicCurve

/--
[AlgebraicCurve_mem_repartitionsOf_iff_coe_mem_adeleBdd](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_mem_repartitionsOf_iff_coe_mem_adeleBdd.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {D : Divisor K F}
  {α : ↥(repartitions K F)} :
-- imply
  α ∈ repartitionsOf D ↔ (α : Place K F → F) ∈ adeleBdd D :=
-- proof
  Iff.rfl


-- created on 2026-10-23
