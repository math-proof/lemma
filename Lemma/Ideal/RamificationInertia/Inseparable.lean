import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RamificationInertia.Inseparable
open scoped Pointwise
open Ideal


/--
[card_inertia_eq_ramificationIdxIn_mul_finInsepDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Inseparable.lean)
-/
@[path]
private lemma card_inertia_eq_ramificationIdxIn_mul_finInsepDegree_eq
  [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B] [IsDomain A] [IsDomain B] [Module.Finite A B] [Module.Flat A B]
  {p : Ideal A} [p.IsMaximal]
  {P : Ideal B} [P.LiesOver p] [P.IsMaximal] :
-- imply
  Nat.card (P.inertia G) =
      ramificationIdxIn p B * Field.finInsepDegree (A ⧸ p) (B ⧸ P) := by
-- proof
  apply Ideal.card_inertia_eq_ramificationIdxIn_mul_finInsepDegree G P


-- created on 2026-10-20
