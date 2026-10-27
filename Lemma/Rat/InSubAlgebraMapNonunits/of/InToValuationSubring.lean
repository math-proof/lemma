import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.AlgebraicCurve.DivisorClassGroup


namespace Definitions
end Definitions
open Definitions
open AlgebraicCurve
open scoped Pointwise


/-- ported from external source -/
@[path]
private lemma main
  [Field κ'] [IsAlgClosed κ'] [Field F'] [Algebra κ' F']
  {P' : Place κ' F'} [P'.FiniteResidue]
  {x : F'}
-- given
  (hx : x ∈ P'.toValuationSubring) :
-- imply
  ∃ c : κ', x - algebraMap κ' F' c ∈ P'.toValuationSubring.nonunits := by
  classical
    have : Module.Finite κ' P'.ResidueField := AlgebraicCurve.Place.FiniteResidue.finite
    have : Algebra.IsIntegral κ' P'.ResidueField := Algebra.IsIntegral.of_finite κ' _
    obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := κ') (K := P'.ResidueField)).2
      (IsLocalRing.residue _ ⟨x, hx⟩)
    refine ⟨c, ?_⟩
    have hmem : (⟨x, hx⟩ : P'.toValuationSubring) - algebraMap κ' P'.toValuationSubring c ∈
      IsLocalRing.maximalIdeal P'.toValuationSubring := by
-- proof
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc,
        IsScalarTower.algebraMap_apply κ' P'.toValuationSubring P'.ResidueField, IsLocalRing.ResidueField.algebraMap_eq,
        sub_self]
    have e : ((⟨x, hx⟩ - algebraMap κ' P'.toValuationSubring c : P'.toValuationSubring) : F') = x - algebraMap κ' F' c := by
      change P'.toValuationSubring.subtype (⟨x, hx⟩ - algebraMap κ' P'.toValuationSubring c) = _
      rw [map_sub]
      rfl
    rw [← e]
    exact ValuationSubring.coe_mem_nonunits_iff.mpr hmem


-- created on 2026-10-24
