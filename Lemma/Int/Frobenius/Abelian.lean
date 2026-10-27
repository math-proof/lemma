import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.RingTheory.Frobenius.Abelian


/--
[arithFrobAt_eq_of_under_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/Abelian.lean)
-/
@[path]
lemma arithFrobAt_eq_of_under_eq
  [CommRing R] [CommRing S] [Algebra R S] [Group G] [MulSemiringAction G S] [SMulCommClass G R S] [Finite G] [Algebra.IsInvariant R S G] [IsMulCommutative G]
  {Q Q' : Ideal S} [Q.IsPrime] [Finite (S ⧸ Q)] [Q'.IsPrime] [Finite (S ⧸ Q')]
-- given
  (h : Q.under R = Q'.under R) :
-- imply
  arithFrobAt R G Q = arithFrobAt R G Q' := by
-- proof
  have hconj := isConj_arithFrobAt R G Q Q' h
  rw [isConj_iff] at hconj
  obtain ⟨c, hc⟩ := hconj
  have htriv : c * arithFrobAt R G Q * c⁻¹ = arithFrobAt R G Q := by
    rw [mul_comm' c (arithFrobAt R G Q), mul_assoc, mul_inv_cancel, mul_one]
  exact htriv.symm.trans hc


-- created on 2026-10-20
-- updated on 2026-10-26
