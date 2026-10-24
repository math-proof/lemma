import Mathlib

universe u

open IsLocalRing

def SmoothFieldFiberRegularStalksInput : Prop :=
  ∀ (k A : Type u) [Field k] [CommRing A] [Algebra k A],
    Algebra.Smooth k A → ∀ (p : Ideal A) [p.IsPrime],
      IsRegularLocalRing (Localization.AtPrime p)

namespace SmoothFieldFiberRegularStalks

theorem isRegularLocalRing_of_isField (R : Type*) [CommRing R] (hf : IsField R) :
    IsRegularLocalRing R := by
  letI := hf.toField
  infer_instance

theorem isRegularLocalRing_localization_atPrime_of_isArtinianRing_of_isReduced
    (A : Type*) [CommRing A] [IsArtinianRing A] [IsReduced A]
    (p : Ideal A) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) :=
  isRegularLocalRing_of_isField _
    (IsArtinianRing.isField_of_isReduced_of_isLocalRing (Localization.AtPrime p))

theorem isRegularRing_of_isArtinianRing_of_isReduced
    (A : Type*) [CommRing A] [IsArtinianRing A] [IsReduced A] :
    IsRegularRing A := by
  refine isRegularRing_iff.mpr ?_
  intro p hp
  exact isRegularLocalRing_localization_atPrime_of_isArtinianRing_of_isReduced A p

theorem isRegularLocalRing_localization_atPrime_of_formallyUnramified
    (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FormallyUnramified k A] [Algebra.EssFiniteType k A]
    (p : Ideal A) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  haveI : Algebra.FormallyUnramified A (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.of_isLocalization (Rₘ := Localization.AtPrime p) p.primeCompl
  haveI : Algebra.FormallyUnramified k (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.comp k A (Localization.AtPrime p)
  haveI : Module.Finite k (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.finite_of_free k (Localization.AtPrime p)
  haveI : IsArtinianRing (Localization.AtPrime p) :=
    IsArtinianRing.of_finite k (Localization.AtPrime p)
  haveI : IsReduced (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.isReduced_of_field k (Localization.AtPrime p)
  exact isRegularLocalRing_of_isField _
    (IsArtinianRing.isField_of_isReduced_of_isLocalRing (Localization.AtPrime p))

theorem isRegularLocalRing_localization_atPrime_of_etale
    (k A : Type*) [Field k] [CommRing A] [Algebra k A] [Algebra.Etale k A]
    (p : Ideal A) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) :=
  isRegularLocalRing_localization_atPrime_of_formallyUnramified k A p

theorem isRegularRing_of_etale
    (k A : Type*) [Field k] [CommRing A] [Algebra k A] [Algebra.Etale k A] :
    IsRegularRing A := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  refine isRegularRing_iff.mpr ?_
  intro p hp
  exact isRegularLocalRing_localization_atPrime_of_etale k A p

theorem smoothFieldFiberRegularStalksInput_iff :
    SmoothFieldFiberRegularStalksInput.{u} ↔
      ∀ (k A : Type u) [Field k] [CommRing A] [Algebra k A],
        Algebra.Smooth k A → ∀ (p : Ideal A) [p.IsPrime],
          IsRegularLocalRing (Localization.AtPrime p) :=
  Iff.rfl

theorem isRegularRing_of_smooth_of_input
    (hinput : SmoothFieldFiberRegularStalksInput.{u})
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A] :
    IsRegularRing A := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  refine isRegularRing_iff.mpr ?_
  intro p hp
  exact hinput k A ‹Algebra.Smooth k A› p

theorem eps_ne_zero (K : Type*) [Field K] : (DualNumber.eps : DualNumber K) ≠ 0 := by
  intro heq
  have h1 := congrArg TrivSqZeroExt.snd heq
  simp at h1

theorem nilradical_dualNumber_eq_span_eps (K : Type*) [Field K] :
    nilradical (DualNumber K) = Ideal.span {(DualNumber.eps : DualNumber K)} := by
  rcases DualNumber.ideal_trichotomy (nilradical (DualNumber K)) with h0 | h1 | h2
  · exfalso
    have hin : (DualNumber.eps : DualNumber K) ∈ nilradical (DualNumber K) :=
      mem_nilradical.mpr DualNumber.isNilpotent_eps
    rw [h0] at hin
    exact eps_ne_zero K (by simpa using hin)
  · exact h1
  · exfalso
    have hone : IsNilpotent (1 : DualNumber K) :=
      mem_nilradical.mp (h2 ▸ Submodule.mem_top)
    obtain ⟨n, hn⟩ := hone
    rw [one_pow] at hn
    exact one_ne_zero hn

theorem ringKrullDim_dualNumber_eq_zero (K : Type*) [Field K] :
    ringKrullDim (DualNumber K) = 0 := by
  haveI : (nilradical (DualNumber K)).IsMaximal := by
    rw [nilradical_dualNumber_eq_span_eps K]
    exact DualNumber.isMaximal_span_singleton_eps
  haveI : Ring.KrullDimLE 0 (DualNumber K) :=
    Ring.KrullDimLE.of_isMaximal_nilradical (DualNumber K)
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

theorem spanFinrank_maximalIdeal_dualNumber_eq_one (K : Type*) [Field K] :
    (maximalIdeal (DualNumber K)).spanFinrank = 1 := by
  rw [DualNumber.maximalIdeal_eq_span_singleton_eps, ← Ideal.submodule_span_eq]
  exact Submodule.spanFinrank_singleton (eps_ne_zero K)

theorem not_isRegularLocalRing_dualNumber (K : Type*) [Field K] :
    ¬ IsRegularLocalRing (DualNumber K) := by
  intro h
  have hspan := h.spanFinrank_maximalIdeal
  rw [ringKrullDim_dualNumber_eq_zero K, spanFinrank_maximalIdeal_dualNumber_eq_one K]
    at hspan
  have h10 : (1 : ℕ) = 0 := by exact_mod_cast hspan
  exact one_ne_zero h10

theorem isField_of_isRegularLocalRing_of_krullDimLE_zero
    (R : Type*) [CommRing R] [Ring.KrullDimLE 0 R] [IsRegularLocalRing R] :
    IsField R := by
  have hspan := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  rw [ringKrullDimZero_iff_ringKrullDim_eq_zero.mp ‹Ring.KrullDimLE 0 R›] at hspan
  have h0 : (maximalIdeal R).spanFinrank = 0 := by exact_mod_cast hspan
  exact IsLocalRing.isField_iff_maximalIdeal_eq.mpr
    ((Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp h0)

theorem not_isRegularLocalRing_localization_atPrime_dualNumber (K : Type*) [Field K] :
    ¬ IsRegularLocalRing (Localization.AtPrime (maximalIdeal (DualNumber K))) := by
  intro h

  haveI : IsNoetherianRing (DualNumber K) := PrincipalIdealRing.isNoetherianRing
  haveI : (nilradical (DualNumber K)).IsMaximal := by
    rw [nilradical_dualNumber_eq_span_eps K]
    exact DualNumber.isMaximal_span_singleton_eps
  haveI : Ring.KrullDimLE 0 (DualNumber K) :=
    Ring.KrullDimLE.of_isMaximal_nilradical (DualNumber K)
  haveI : IsArtinianRing (DualNumber K) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

  have hf : IsField (Localization.AtPrime (maximalIdeal (DualNumber K))) :=
    isField_of_isRegularLocalRing_of_krullDimLE_zero
      (Localization.AtPrime (maximalIdeal (DualNumber K)))
  letI := hf.toField
  have hz : algebraMap (DualNumber K)
      (Localization.AtPrime (maximalIdeal (DualNumber K))) DualNumber.eps = 0 :=
    (DualNumber.isNilpotent_eps.map (algebraMap (DualNumber K)
      (Localization.AtPrime (maximalIdeal (DualNumber K))))).eq_zero

  obtain ⟨⟨m, hm⟩, hm'⟩ := (IsLocalization.map_eq_zero_iff
    (maximalIdeal (DualNumber K)).primeCompl
    (Localization.AtPrime (maximalIdeal (DualNumber K))) DualNumber.eps).mp hz
  have hu : IsUnit m := by
    by_contra hnu
    exact hm ((IsLocalRing.mem_maximalIdeal m).mpr hnu)
  exact eps_ne_zero K (hu.mul_right_eq_zero.mp hm')

theorem not_forall_regular_stalks_without_smooth :
    ¬ (∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (p : Ideal A) [p.IsPrime],
        IsRegularLocalRing (Localization.AtPrime p)) := by
  intro hclaim
  exact not_isRegularLocalRing_localization_atPrime_dualNumber ℚ
    (hclaim ℚ (DualNumber ℚ) (maximalIdeal (DualNumber ℚ)))

end SmoothFieldFiberRegularStalks

/--
info: 'SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_isArtinianRing_of_isReduced' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_isArtinianRing_of_isReduced

/--
info: 'SmoothFieldFiberRegularStalks.isRegularRing_of_isArtinianRing_of_isReduced' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.isRegularRing_of_isArtinianRing_of_isReduced

/--
info: 'SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_formallyUnramified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_formallyUnramified

/--
info: 'SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_etale' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_etale

/--
info: 'SmoothFieldFiberRegularStalks.isRegularRing_of_etale' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.isRegularRing_of_etale

/--
info: 'SmoothFieldFiberRegularStalks.isRegularRing_of_smooth_of_input' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.isRegularRing_of_smooth_of_input

/--
info: 'SmoothFieldFiberRegularStalks.not_isRegularLocalRing_dualNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.not_isRegularLocalRing_dualNumber

/--
info: 'SmoothFieldFiberRegularStalks.not_isRegularLocalRing_localization_atPrime_dualNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.not_isRegularLocalRing_localization_atPrime_dualNumber

/--
info: 'SmoothFieldFiberRegularStalks.not_forall_regular_stalks_without_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.not_forall_regular_stalks_without_smooth
