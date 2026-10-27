import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.AlgebraicCurve_PlaceEvaluation
import Lemma.Int.P2MUtil


namespace Definitions
end Definitions
open Definitions
open IsLocalRing AlgebraicCurve
open Int


/--
[AlgebraicCurve_Place_evalAt_algebraMap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Place_evalAt_algebraMap.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {v : Place K F}
  {a : K} :
-- imply
  v.evalAt (algebraMap K F a) = a := by
-- proof
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have ha : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring) = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [ha, ← ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
    v.residueInv_algebraMap]


-- created on 2026-10-24
