-- Carved from Lemma/Definitions/Def_ExtCitation_LocalLevelSubgroupsPD.lean: instance decls only.
import Mathlib
set_option autoImplicit false

open ExtCitation

namespace ExtCitation


instance levelSubgroup_normal (q : Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    ((F.fixingSubgroup).comap (primeLocalToGlobal q)).Normal := by
  rw [levelSubgroup_eq_ker]; exact MonoidHom.normal_ker _

instance levelSubgroup_finiteIndex (q : Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [Normal ℚ F] :
    ((F.fixingSubgroup).comap (primeLocalToGlobal q)).FiniteIndex := by
  rw [levelSubgroup_eq_ker]; exact Subgroup.finiteIndex_ker _


instance inertiaPullback_normal (q : Nat.Primes) :
    (((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)).Normal := by

  let D := (primeLocalPlace q).decompositionSubgroup ℚ
  have hD : ∀ g : primeLocalGaloisGroup q, primeLocalToGlobal q g ∈ D := primeLocalToGlobal_mem_decompositionSubgroup q
  let r' : primeLocalGaloisGroup q →* D := (primeLocalToGlobal q).codRestrict D hD
  have : ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)
      = (((primeLocalPlace q).inertiaSubgroup ℚ)).comap r' := by
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_comap, ValuationSubring.inertiaSubgroupIn, Subgroup.mem_map]
    constructor
    · rintro ⟨τ, hτ, hτg⟩
      have : r' g = τ := Subtype.ext hτg.symm
      rwa [this]
    · intro h; exact ⟨r' g, h, rfl⟩
  rw [this, ValuationSubring.inertiaSubgroup, MonoidHom.comap_ker]
  exact MonoidHom.normal_ker _

end ExtCitation
