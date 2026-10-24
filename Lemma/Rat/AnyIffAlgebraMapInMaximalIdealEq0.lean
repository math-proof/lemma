import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Subring_exists_valuationSubring_mem_maximalIdeal_iff_apply_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Subring_exists_valuationSubring_mem_maximalIdeal_iff_apply_eq_zero.lean)
-/
@[path]
private lemma main
  (K Kbar : Type) [Field K] [Field Kbar] [Algebra K Kbar] (B : Subring K)
    (Ω : Type) [Field Ω] (ψ : ↥B →+* Ω) :
    -- imply
    ∃ (O : ValuationSubring Kbar) (hB : ∀ b : ↥B, algebraMap K Kbar (b : K) ∈ O),
      ∀ b : ↥B, (⟨algebraMap K Kbar (b : K), hB b⟩ : ↥O) ∈ IsLocalRing.maximalIdeal ↥O ↔ ψ b = 0 := by
    -- proof
  classical
  set p : Ideal ↥B := RingHom.ker ψ with hp
  let hprime : p.IsPrime := RingHom.ker_isPrime ψ
  set g : ↥B →+* Kbar := (algebraMap K Kbar).comp B.subtype with hg
  have hgapp : ∀ b : ↥B, g b = algebraMap K Kbar (b : K) := fun b => rfl
  have hgunit : ∀ y : ↥p.primeCompl, IsUnit (g (y : ↥B)) := by
    intro y
    rw [isUnit_iff_ne_zero, hgapp, map_ne_zero_iff _ (algebraMap K Kbar).injective]
    intro hy0
    apply y.2
    show (y : ↥B) ∈ RingHom.ker ψ
    rw [RingHom.mem_ker, show (y : ↥B) = 0 from Subtype.ext hy0, map_zero]
  set f : Localization.AtPrime p →+* Kbar := IsLocalization.lift (M := p.primeCompl) hgunit with hf
  have hfalg : ∀ b : ↥B, f (algebraMap ↥B (Localization.AtPrime p) b) = algebraMap K Kbar (b : K) :=
    fun b => IsLocalization.lift_eq hgunit b
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  have hB : ∀ b : ↥B, algebraMap K Kbar (b : K) ∈ O := by
    intro b
    rw [← hfalg, ← ValuationSubring.mem_toSubring]
    apply hO _
  refine ⟨O, hB, fun b => ?_⟩
  have hel : (⟨algebraMap K Kbar (b : K), hB b⟩ : ↥O) =
      ⟨(f.codRestrict O.toSubring hO) (algebraMap ↥B (Localization.AtPrime p) b), (hO _)⟩ := by
    apply Subtype.ext
    show algebraMap K Kbar (b : K) = f (algebraMap ↥B (Localization.AtPrime p) b)
    rw [hfalg]
  constructor
  ·
    intro hm
    by_contra hb
    have hbp : b ∈ p.primeCompl := (fun hb' => hb ((RingHom.mem_ker).mp hb') : b ∉ p)
    have hu : IsUnit (algebraMap ↥B (Localization.AtPrime p) b) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p b).mpr hbp
    have hu' : IsUnit ((f.codRestrict O.toSubring hO) (algebraMap ↥B (Localization.AtPrime p) b)) := hu.map _
    have hu'' : IsUnit (⟨algebraMap K Kbar (b : K), hB b⟩ : ↥O) := by
      rw [hel]; apply hu'
    refine (IsLocalRing.mem_maximalIdeal _).mp hm hu''
  ·
    intro hb
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hnot : ¬ IsUnit (algebraMap ↥B (Localization.AtPrime p) b) := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p b]
      intro hbp; apply (hbp : b ∉ p) ((RingHom.mem_ker).mpr hb)
    refine hnot ?_
    apply hloc.map_nonunit
    rw [hel] at hu
    apply hu


-- created on 2026-10-20
