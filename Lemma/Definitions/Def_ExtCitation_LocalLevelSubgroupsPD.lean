import Mathlib
import Lemma.Definitions.Def_ExtEndgame_ProductionDatum

set_option autoImplicit false

open ExtCitation

namespace ExtCitation

theorem primeLocalToGlobal_mem_decompositionSubgroup (q : Nat.Primes) (g : primeLocalGaloisGroup q) :
    primeLocalToGlobal q g ∈ (primeLocalPlace q).decompositionSubgroup ℚ := by
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  exact localGaloisToGlobal_mem_decompositionSubgroup (q : ℕ) g

theorem levelSubgroup_eq_ker (q : Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    (F.fixingSubgroup).comap (primeLocalToGlobal q)
      = ((AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).comp (primeLocalToGlobal q)).ker := by
  rw [← @IntermediateField.restrictNormalHom_ker ℚ (AlgebraicClosure ℚ) _ _ _ F ‹Normal ℚ F›, MonoidHom.comap_ker]
  rfl

instance levelSubgroup_normal (q : Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    ((F.fixingSubgroup).comap (primeLocalToGlobal q)).Normal := by
  rw [levelSubgroup_eq_ker]; exact MonoidHom.normal_ker _

instance levelSubgroup_finiteIndex (q : Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [Normal ℚ F] :
    ((F.fixingSubgroup).comap (primeLocalToGlobal q)).FiniteIndex := by
  rw [levelSubgroup_eq_ker]; exact Subgroup.finiteIndex_ker _

theorem levelSubgroup_antitone (q : Nat.Primes) {F F' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : F ≤ F') :
    (F'.fixingSubgroup).comap (primeLocalToGlobal q) ≤ (F.fixingSubgroup).comap (primeLocalToGlobal q) :=
  Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone h)

theorem mem_inertiaPullback_iff (q : Nat.Primes) (g : primeLocalGaloisGroup q) :
    g ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q) ↔
      ∀ x : IsLocalRing.ResidueField (primeLocalPlace q),
        (⟨primeLocalToGlobal q g, primeLocalToGlobal_mem_decompositionSubgroup q g⟩ :
          (primeLocalPlace q).decompositionSubgroup ℚ) • x = x := by
  rw [Subgroup.mem_comap, ValuationSubring.inertiaSubgroupIn, Subgroup.mem_map]
  constructor
  · rintro ⟨τ, hτ, hτg⟩
    intro x
    have hmem : (⟨primeLocalToGlobal q g, primeLocalToGlobal_mem_decompositionSubgroup q g⟩ : (primeLocalPlace q).decompositionSubgroup ℚ) = τ := by
      apply Subtype.ext; exact hτg.symm
    rw [hmem]
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hτ
    have := congrArg (fun φ => (φ : IsLocalRing.ResidueField (primeLocalPlace q) ≃+* _) x) hτ
    simpa using this
  · intro h
    refine ⟨⟨primeLocalToGlobal q g, primeLocalToGlobal_mem_decompositionSubgroup q g⟩, ?_, rfl⟩
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro x
    simpa using h x

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
