import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.Frobenius.Abelian


/--
[arithFrobAt_eq_of_under_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/Abelian.lean)
-/
@[path]
private lemma arithFrobAt_eq_of_under_eq_eq
  [CommRing R] [CommRing S] [Algebra R S] [Group G] [MulSemiringAction G S] [SMulCommClass G R S] [Finite G] [Algebra.IsInvariant R S G] [IsMulCommutative G]
  {Q Q' : Ideal S} [Q.IsPrime] [Finite (S ⧸ Q)] [Q'.IsPrime] [Finite (S ⧸ Q')]
-- given
  (h : Q.under R = Q'.under R) :
-- imply
  arithFrobAt R G Q = arithFrobAt R G Q' := by
-- proof
  apply arithFrobAt_eq_of_under_eq Q Q' h


-- created on 2026-10-20
