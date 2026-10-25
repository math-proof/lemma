import Mathlib
import sympy.Basic
import Lemma.AlgebraicCurve.DivisorClassGroup
open AlgebraicCurve


/-- ported from external source -/

private noncomputable def placeSubalgebra {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
  Subalgebra K F :=
  { v.toValuationSubring.toSubring.toSubsemiring with algebraMap_mem' := v.algebraMap_mem' }

private lemma mem_placeSubalgebra {K F : Type*} [Field K] [Field F] [Algebra K F]
  (v : Place K F) {y : F} :
  y ∈ placeSubalgebra v ↔ y ∈ v.toValuationSubring := Iff.rfl

private lemma valuationSubring_integers {K F : Type*} [Field K] [Field F] [Algebra K F]
  (v : Place K F) :
  (v.toValuationSubring.valuation).Integers v.toValuationSubring :=
  { hom_inj := Subtype.coe_injective
    map_le_one := fun a => v.toValuationSubring.valuation_le_one a
    exists_of_le_one := fun {r} hr =>
      ⟨⟨r, v.toValuationSubring.mem_of_valuation_le_one r hr⟩, rfl⟩ }

private lemma mem_of_isIntegral_adjoin {K F : Type*} [Field K] [Field F] [Algebra K F]
  (v : Place K F) {j x : F} (hj : j ∈ v.toValuationSubring)
  (hx : IsIntegral (Algebra.adjoin K {j}) x) : x ∈ v.toValuationSubring := by
  have hle : Algebra.adjoin K {j} ≤ placeSubalgebra v :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr ((mem_placeSubalgebra v).mpr hj))
  let φ' : ↥(Algebra.adjoin K {j}) →+* ↥v.toValuationSubring :=
    { toFun := fun a => ⟨(a : F), (mem_placeSubalgebra v).mp (hle a.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hOx : IsIntegral ↥v.toValuationSubring x :=
    IsIntegral.map_of_comp_eq φ' (RingHom.id F) (by ext a; rfl) hx
  refine v.toValuationSubring.mem_of_valuation_le_one x
    ((valuationSubring_integers v).isIntegral_iff_v_le_one.mp hOx)
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {v : Place K F}
  {j x : F}
-- given
  (hj : j ∈ v.toValuationSubring)
  (hx : IsIntegral (Algebra.adjoin K {j}) x) :
-- imply
  x ∈ v.toValuationSubring :=
-- proof
  mem_of_isIntegral_adjoin v hj hx


-- created on 2026-10-23
