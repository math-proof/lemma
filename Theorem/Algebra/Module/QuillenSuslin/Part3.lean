/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Ring
import Def.Algebra.Module.QuillenSuslin.Part3
/-!
# Quillen–Suslin theorem

Formalizes that every finitely generated projective module over a polynomial ring over a field is
free.
The proof uses idempotent matrices, Roberts' local proof of Horrocks' theorem, Quillen patching,
and induction on the number of variables.
-/


namespace QuillenSuslin

universe u v

theorem qsPolynomialPart_algebraMap
    {R : Type*} [CommRing R] [Nontrivial R]
    (p : Polynomial R) :
    qsPolynomialPart R
        (algebraMap (Polynomial R) (Localization (qsMonicSubmonoid R)) p) = p := by
  change p /ₘ (1 : Polynomial R) = p
  exact Polynomial.divByMonic_one p

theorem qs_exists_monic_lift
    {R S : Type*} [CommRing R] [CommRing S] [Nontrivial R] [Nontrivial S]
    (f : R →+* S) (hf : Function.Surjective f)
    {p : Polynomial S} (hp : p.Monic) :
    ∃ q : Polynomial R, q.Monic ∧ q.map f = p := by
  let n := p.natDegree
  have hpdeg : p.degree = ((Polynomial.X : Polynomial S) ^ n).degree := by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero, Polynomial.degree_X_pow]
  have hplc : p.leadingCoeff =
      ((Polynomial.X : Polynomial S) ^ n).leadingCoeff := by
    simp [hp.leadingCoeff]
  have hlower : (p - (Polynomial.X : Polynomial S) ^ n).degree < (n : WithBot ℕ) := by
    simpa [Polynomial.degree_eq_natDegree hp.ne_zero] using
      Polynomial.degree_sub_lt_left hpdeg hp.ne_zero hplc
  obtain ⟨q₀, hq₀⟩ := Polynomial.map_surjective f hf
    (p - (Polynomial.X : Polynomial S) ^ n)
  let q := (Polynomial.X : Polynomial R) ^ n +
    q₀ %ₘ (Polynomial.X : Polynomial R) ^ n
  refine ⟨q, Polynomial.monic_X_pow_add ?_, ?_⟩
  · simpa only [Polynomial.degree_X_pow] using
      Polynomial.degree_modByMonic_lt q₀ (Polynomial.monic_X_pow n)
  · dsimp only [q]
    rw [Polynomial.map_add,
      Polynomial.map_modByMonic f (Polynomial.monic_X_pow n), hq₀]
    simp only [Polynomial.map_pow, Polynomial.map_X]
    rw [(Polynomial.modByMonic_eq_self_iff (Polynomial.monic_X_pow n)).mpr <| by
      simpa only [Polynomial.degree_X_pow] using hlower]
    ring

theorem qs_map_monicSubmonoid_eq
    {R S : Type*} [CommRing R] [CommRing S] [Nontrivial R] [Nontrivial S]
    (f : R →+* S) (hf : Function.Surjective f) :
    (qsMonicSubmonoid R).map (Polynomial.mapRingHom f) = qsMonicSubmonoid S := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq.map f
  · intro hp
    obtain ⟨q, hq, rfl⟩ := qs_exists_monic_lift f hf hp
    exact Submonoid.mem_map_of_mem _ hq

theorem qs_monicLocalization_isFractionRing
    (k : Type*) [Field k] :
    IsFractionRing (Polynomial k) (Localization (qsMonicSubmonoid k)) := by
  apply (IsLocalization.iff_of_le_of_exists_dvd
    (M := qsMonicSubmonoid k) (S := Localization (qsMonicSubmonoid k))
    (nonZeroDivisors (Polynomial k)) ?_ ?_).mp
  · exact Localization.isLocalization
  · intro p hp
    exact hp.mem_nonZeroDivisors
  · intro p hp
    have hp0 : p ≠ 0 :=
      mem_nonZeroDivisors_iff_ne_zero.mp hp
    let q := p * Polynomial.C p.leadingCoeff⁻¹
    refine ⟨q, Polynomial.monic_mul_leadingCoeff_inv hp0, ?_⟩
    exact ⟨Polynomial.C p.leadingCoeff⁻¹, rfl⟩

theorem qs_nonzero_polynomial_maps_to_unit
    {k A : Type*} [Field k] [CommRing A] [Nontrivial A]
    (f : k →+* A) {p : Polynomial k} (hp : p ≠ 0) :
    IsUnit (((algebraMap (Polynomial A)
      (Localization (qsMonicSubmonoid A))).comp
        (Polynomial.mapRingHom f)) p) := by
  let p' := p * Polynomial.C p.leadingCoeff⁻¹
  have hp' : p'.Monic := Polynomial.monic_mul_leadingCoeff_inv hp
  let s : qsMonicSubmonoid A := ⟨p'.map f, hp'.map f⟩
  have hmonic : IsUnit (algebraMap (Polynomial A)
      (Localization (qsMonicSubmonoid A)) (s : Polynomial A)) :=
    IsLocalization.map_units _ s
  have hlc : IsUnit (f p.leadingCoeff) :=
    (isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)).map f
  have hconstant : IsUnit (algebraMap (Polynomial A)
      (Localization (qsMonicSubmonoid A))
        (Polynomial.C (f p.leadingCoeff))) :=
    (Polynomial.isUnit_C.mpr hlc).map
      (algebraMap (Polynomial A) (Localization (qsMonicSubmonoid A)))
  have hpdecomp : p' * Polynomial.C p.leadingCoeff = p := by
    simp only [p', mul_assoc, ← Polynomial.C_mul]
    rw [inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hp), map_one, mul_one]
  rw [← hpdecomp, map_mul]
  change IsUnit
    (algebraMap (Polynomial A) (Localization (qsMonicSubmonoid A))
        (p'.map f) *
      algebraMap (Polynomial A) (Localization (qsMonicSubmonoid A))
        ((Polynomial.C p.leadingCoeff).map f))
  simpa [s] using hmonic.mul hconstant

end QuillenSuslin
