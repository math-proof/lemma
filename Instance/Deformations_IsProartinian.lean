-- Carved from Lemma/Definitions/Def_Deformations_IsProartinian.lean: instance decls only.
import Mathlib
import Class.Patching_SystemTypes
import Instance.Deformations_Deformations_Lemmas

set_option autoImplicit false


section AdicTopology

variable (R : Type*) [CommRing R] [IsLocalRing R] [TopologicalSpace R] [IsTopologicalRing R]

namespace IsLocalRing

variable [IsAdicTopology R]

instance (priority := 100) :
    NonarchimedeanRing R :=
  IsLocalRing.IsAdicTopology.isAdic (R := R) ▸ RingSubgroupsBasis.nonarchimedean _


instance (priority := 100) : IsLinearTopology R R := .mk_of_hasBasis _ (hasBasis_maximalIdeal_pow R)

instance (priority := 100) [IsNoetherianRing R] : T2Space R := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  rintro x (hx : x ∉ (⊥ : Ideal R))
  rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top] at hx
  obtain ⟨n, hn⟩ : ∃ n, x ∉ maximalIdeal R ^ n := by simpa using hx
  exact ⟨_, (isOpen_maximalIdeal_pow'' R n).mem_nhds (zero_mem _), hn⟩

instance (priority := 100) [IsArtinianRing R] : DiscreteTopology R := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  convert isOpen_maximalIdeal_pow'' R n
  rw [← jacobson_eq_maximalIdeal _ bot_ne_top, hn]
  rfl

instance (n : ℕ) : DiscreteTopology (R ⧸ maximalIdeal R ^ n) :=
  QuotientAddGroup.discreteTopology (isOpen_maximalIdeal_pow'' R n)

instance [IsNoetherianRing R] : IsHausdorff (maximalIdeal R) R where
  haus' x hx := show x ∈ (⊥ : Ideal R) by
    rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top]
    simpa [SModEq.zero] using hx

instance [CompactSpace R] : IsPrecomplete (maximalIdeal R) R where
  prec' f H := by
    simp_rw [← Ideal.one_eq_top, smul_eq_mul, mul_one] at H
    have : ∀ i, T2Space (R ⧸ (maximalIdeal R) ^ i) := inferInstance
    have := AdicTopologyAux.denseRange_inverseLimit (ι := ℕᵒᵈ) (R ⧸ maximalIdeal R ^ ·)
      (fun i j h ↦ Ideal.quotientMap _ (.id R) (by exact Ideal.pow_le_pow_right h))
      (fun i j h ↦ continuous_coinduced_dom.mpr (continuous_algebraMap _ _))
      (fun x : R ↦ ⟨fun i ↦ algebraMap _ _ x, by simp⟩)
      (fun i ↦ (Ideal.Quotient.mk_surjective).denseRange)
    have := ((isCompact_range (Continuous.subtype_mk (continuous_pi
      fun i ↦ continuous_algebraMap _ _) _)).isClosed.closure_eq.symm.trans
      this.closure_eq).ge (Set.mem_univ <| by exact ⟨fun i ↦ f i, fun i j e ↦ by
        have h := (H e).symm; rw [SModEq.def] at h; exact h⟩)
    have this' : ∃ y, ∀ a : ℕ, Ideal.Quotient.mk (maximalIdeal R ^ a) (f (OrderDual.toDual a)) =
        Ideal.Quotient.mk _ y := by
      simp [funext_iff, eq_comm (b := Ideal.Quotient.mk _ (f _))] at this
      exact this
    obtain ⟨y, hy⟩ := this'
    refine ⟨y, fun n => ?_⟩
    simp_rw [← Ideal.one_eq_top, smul_eq_mul, mul_one]
    exact SModEq.sub_mem.mpr (Ideal.Quotient.eq.mp (hy n))


instance {R} [CommRing R] [IsLocalRing R] : IsAdicTopology R := ⟨rfl⟩

end IsLocalRing

end AdicTopology

section Proartinian

variable {R S : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]


instance [DiscreteTopology R] [IsArtinianRing R] : IsProartinian R := by
  rwa [isProartinian_iff_isArtinianRing]

instance [IsLocalRing R] [IsLocalRing.IsAdicTopology R] [IsNoetherianRing R] [CompactSpace R] :
    IsProartinian R where
  isArtinianRing_quotient I hI :=
    have : Finite (R ⧸ I) := AddSubgroup.quotient_finite_of_isOpen _ hI
    inferInstance


end Proartinian
