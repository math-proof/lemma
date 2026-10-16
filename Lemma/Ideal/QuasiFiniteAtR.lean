import Mathlib
import sympy.Basic


private lemma quasiFiniteAt_of_forall_eq
  [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
  {𝔮 : Ideal S} [𝔮.IsPrime]
-- given
  (hmin : ∀ P : Ideal S, P.IsPrime → P ≤ 𝔮 →
    P.comap (algebraMap R S) = 𝔮.comap (algebraMap R S) → P = 𝔮)
  (hmax : ∀ P : Ideal S, P.IsPrime → 𝔮 ≤ P →
    P.comap (algebraMap R S) = 𝔮.comap (algebraMap R S) → P = 𝔮) :
-- imply
  Algebra.QuasiFiniteAt R 𝔮 := by
-- proof
  classical
  let q : PrimeSpectrum S := ⟨𝔮, ‹_›⟩
  let p : PrimeSpectrum R := q.comap (algebraMap R S)
  have hq : q ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} := rfl
  let x : ↥(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}) := ⟨q, hq⟩
  have hxmax : IsMax x := by
    rintro ⟨y, hy⟩ hxy
    have hy' : PrimeSpectrum.comap (algebraMap R S) y = p := hy
    have hle : 𝔮 ≤ y.asIdeal := hxy
    have hcomap : y.asIdeal.comap (algebraMap R S) = 𝔮.comap (algebraMap R S) :=
      congrArg PrimeSpectrum.asIdeal hy'
    have := hmax y.asIdeal y.2 hle hcomap
    change y ≤ q
    apply le_of_eq
    apply PrimeSpectrum.ext
    apply this
  have hxmin : IsMin x := by
    rintro ⟨y, hy⟩ hyx
    have hy' : PrimeSpectrum.comap (algebraMap R S) y = p := hy
    have hle : y.asIdeal ≤ 𝔮 := hyx
    have hcomap : y.asIdeal.comap (algebraMap R S) = 𝔮.comap (algebraMap R S) :=
      congrArg PrimeSpectrum.asIdeal hy'
    have := hmin y.asIdeal y.2 hle hcomap
    change q ≤ y
    apply le_of_eq
    apply PrimeSpectrum.ext
    apply this.symm
  refine Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber q ?_
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  rw [← e.isOpen_image, Set.image_singleton]
  let _ : IsNoetherianRing (p.asIdeal.Fiber S) :=
    Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField _
  let _ : IsJacobsonRing (p.asIdeal.Fiber S) :=
    isJacobsonRing_of_finiteType (A := p.asIdeal.ResidueField)
  have hex : e x = PrimeSpectrum.preimageOrderIsoFiber R S p x := rfl
  have htfae :=
    (PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing (e x)).out 1 3
  rw [htfae]
  refine ⟨?_, ?_⟩
  ·
    rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal, ← PrimeSpectrum.isMax_iff, hex,
      OrderIso.isMax_apply]
    apply hxmax
  ·
    rw [PrimeSpectrum.stableUnderGeneralization_singleton, ← PrimeSpectrum.isMin_iff, hex,
      OrderIso.isMin_apply]
    apply hxmin


/--
[Algebra_QuasiFiniteAt_of_minimal_of_maximal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_QuasiFiniteAt_of_minimal_of_maximal.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
  {𝔮 : Ideal S} [𝔮.IsPrime]
-- given
  (hmin : Minimal
    (fun P : Ideal S => P.IsPrime ∧ P.comap (algebraMap R S) = 𝔮.comap (algebraMap R S)) 𝔮)
  (hmax : Maximal
    (fun P : Ideal S => P.IsPrime ∧ P.comap (algebraMap R S) = 𝔮.comap (algebraMap R S)) 𝔮) :
-- imply
  Algebra.QuasiFiniteAt R 𝔮 :=
-- proof
  quasiFiniteAt_of_forall_eq
    (fun _ hP hle hc => le_antisymm hle (hmin.2 ⟨hP, hc⟩ hle))
    (fun _ hP hle hc => le_antisymm (hmax.2 ⟨hP, hc⟩ hle) hle)


-- created on 2026-10-13
