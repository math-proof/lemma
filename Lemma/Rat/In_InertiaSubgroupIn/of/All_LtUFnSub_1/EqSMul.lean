import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.FLTPrelim_Ramification
import Lemma.Int.P2MUtil


namespace Definitions
end Definitions
open Definitions
open scoped Pointwise
open Int


/--
[ValuationSubring_mem_inertiaSubgroupIn_of_valuation_sub_lt_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_mem_inertiaSubgroupIn_of_valuation_sub_lt_one.lean)
-/
@[path]
private lemma main
  [Field K] [Field L] [Algebra K L]
  {A : ValuationSubring L}
  {σ : L ≃ₐ[K] L}
-- given
  (hσA : σ • A = A)
  (h : ∀ a ∈ A, A.valuation (σ a - a) < 1) :
-- imply
  σ ∈ A.inertiaSubgroupIn K := by
-- proof
  let d : A.decompositionSubgroup K := ⟨σ, hσA⟩
  refine ⟨d, ?_, rfl⟩
  change (MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A)) d = 1
  ext x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  change d • IsLocalRing.residue A a = IsLocalRing.residue A a
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ValuationSubring.valuation_lt_one_iff]
  exact h a a.2


-- created on 2026-10-24
