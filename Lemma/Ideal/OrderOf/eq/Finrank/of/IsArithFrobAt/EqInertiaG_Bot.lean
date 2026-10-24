import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_ArithFrobResidue
open scoped Pointwise


/-- ported from external source -/
@[path]
private lemma main
  [CommRing A] [CommRing B] [Algebra A B] [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
  {P : Ideal B} [P.IsMaximal] [(P.under A).IsMaximal] [Fintype (A ⧸ P.under A)] [Finite (B ⧸ P)]
  {σ : MulAction.stabilizer G P}
-- given
  (hP : P.inertia G = ⊥)
  (hσ : IsArithFrobAt A (σ : G) P) :
-- imply
  orderOf (σ : G) = Module.finrank (A ⧸ P.under A) (B ⧸ P) :=
-- proof
  ArithFrobResidue.orderOf_arithFrob_eq_finrank_of_inertia_eq_bot hP σ hσ


-- created on 2026-10-24
