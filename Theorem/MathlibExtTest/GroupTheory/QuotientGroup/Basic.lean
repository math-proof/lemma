/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GroupTheory/QuotientGroup/Basic.lean -/


import Theorem.GroupTheory.QuotientGroup.Basic
import Lemma.Nat.EqQuotientEquivRangeQuotient.of.LeKer
import Mathlib.Data.ZMod.Basic
import Def.MathlibExtTest.GroupTheory.QuotientGroup.Basic
/-!
# Tests for `QuotientGroup.quotientEquivRangeQuotient`

Usage tests for the canonical isomorphism between the quotient by a subgroup
containing a homomorphism kernel and the corresponding quotient of the range,
covering the multiplicative API, the additive API, and representative
evaluation on the concrete reduction-mod-two map.
-/


namespace QuotientEquivRangeTest

/-- Multiplicative API on a concrete map with `B = ⊤`. -/
noncomputable example :
    Multiplicative ℤ ⧸ (⊤ : Subgroup (Multiplicative ℤ)) ≃*
      phi.range ⧸ ((⊤ : Subgroup (Multiplicative ℤ)).map phi).subgroupOf
        phi.range :=
  QuotientGroup.quotientEquivRangeQuotient phi ⊤ le_top

/-- Multiplicative API on a concrete map with `B` equal to the kernel. -/
noncomputable example :
    Multiplicative ℤ ⧸ phi.ker ≃*
      phi.range ⧸ (phi.ker.map phi).subgroupOf phi.range :=
  QuotientGroup.quotientEquivRangeQuotient phi phi.ker le_rfl

/-- Representative evaluation via the simp lemma. -/
example (a : Multiplicative ℤ) :
    QuotientGroup.quotientEquivRangeQuotient phi ⊤ le_top
        (QuotientGroup.mk a) =
      QuotientGroup.mk (phi.rangeRestrict a) :=
  QuotientGroup.quotientEquivRangeQuotient_mk phi ⊤ le_top a

/-- Representative evaluation by the simplifier. -/
example (a : Multiplicative ℤ) :
    QuotientGroup.quotientEquivRangeQuotient phi ⊤ le_top
        (QuotientGroup.mk a) =
      QuotientGroup.mk (phi.rangeRestrict a) := by
  simp

/-- Representative evaluation holds definitionally. -/
example (a : Multiplicative ℤ) :
    QuotientGroup.quotientEquivRangeQuotient phi ⊤ le_top
        (QuotientGroup.mk a) =
      QuotientGroup.mk (phi.rangeRestrict a) :=
  rfl

/-- The constructed equivalence is bijective. -/
example :
    Function.Bijective
      (QuotientGroup.quotientEquivRangeQuotient phi ⊤ le_top) :=
  (QuotientGroup.quotientEquivRangeQuotient phi ⊤ le_top).bijective

/-- Additive API on a concrete map with `B = ⊤`. -/
noncomputable example :
    ℤ ⧸ (⊤ : AddSubgroup ℤ) ≃+
      psi.range ⧸ ((⊤ : AddSubgroup ℤ).map psi).addSubgroupOf psi.range :=
  QuotientAddGroup.quotientEquivRangeQuotient psi ⊤ le_top

/-- Additive API on a concrete map with `B` equal to the kernel. -/
noncomputable example :
    ℤ ⧸ psi.ker ≃+ psi.range ⧸ (psi.ker.map psi).addSubgroupOf psi.range :=
  QuotientAddGroup.quotientEquivRangeQuotient psi psi.ker le_rfl

/-- Representative evaluation via the additive simp lemma. -/
example (a : ℤ) :
    QuotientAddGroup.quotientEquivRangeQuotient psi ⊤ le_top
        (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (psi.rangeRestrict a) :=
  QuotientAddGroup.quotientEquivRangeQuotient_mk psi ⊤ le_top a

/-- Representative evaluation by the simplifier, additive version. -/
example (a : ℤ) :
    QuotientAddGroup.quotientEquivRangeQuotient psi ⊤ le_top
        (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (psi.rangeRestrict a) := by
  simp

end QuotientEquivRangeTest
