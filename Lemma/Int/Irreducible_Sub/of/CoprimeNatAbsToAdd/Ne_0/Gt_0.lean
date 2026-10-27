import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial


/--
[Polynomial_irreducible_X_pow_sub_C_of_monoidHom_units_coprime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_irreducible_X_pow_sub_C_of_monoidHom_units_coprime.lean)
-/
@[path]
private lemma main
  {K : Type u} [Field K]
  {N : ℕ}
  {β : K}
  {φ : Kˣ →* Multiplicative ℤ}
-- given
  (hN : 0 < N)
  (hβ : β ≠ 0)
  (hφ : (Multiplicative.toAdd (φ (Units.mk0 β hβ))).natAbs.Coprime N) :
-- imply
  Irreducible (X ^ N - C β) := by
-- proof
  classical
    set P : K[X] := X ^ N - C β with hP
    have hN0 : N ≠ 0 := hN.ne'
    have hPmonic : P.Monic := monic_X_pow_sub_C β hN0
    have hPdeg : P.natDegree = N := natDegree_X_pow_sub_C
    have hPdeg' : P.degree ≠ 0 := by
      rwa [degree_X_pow_sub_C hN, Ne, Nat.cast_eq_zero]
    let L := P.SplittingField
    have hPmapdeg : (P.map (algebraMap K L)).degree ≠ 0 := by
      rwa [degree_map]
    obtain ⟨α, hα⟩ := (SplittingField.splits P).exists_eval_eq_zero hPmapdeg
    have hαP : aeval α P = 0 := by rwa [aeval_def, ← eval_map]
    have hαN : α ^ N = algebraMap K L β := by
      have h1 : aeval α (X ^ N - C β : K[X]) = 0 := hαP
      rwa [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h1
    have hα0 : α ≠ 0 := by
      intro h
      rw [h, zero_pow hN0, eq_comm, map_eq_zero] at hαN
      exact hβ hαN
    have hint : IsIntegral K α := ⟨P, hPmonic, by rwa [← aeval_def]⟩
    set q : K[X] := minpoly K α with hq
    have hqirr : Irreducible q := minpoly.irreducible hint
    have hqmonic : q.Monic := minpoly.monic hint
    have hqdvd : q ∣ P := minpoly.dvd K α hαP
    let E := IntermediateField.adjoin K ({α} : Set L)
    let γ : E := IntermediateField.AdjoinSimple.gen K α
    have hγ : (γ : L) = α := IntermediateField.AdjoinSimple.algebraMap_gen K α
    have hγN : γ ^ N = algebraMap K E β := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, hγ, hαN]
      rfl
    have hγ0 : γ ≠ 0 := by
      intro h
      apply hα0
      rw [← hγ, h]
      rfl
    have : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hint
    have hd : Module.finrank K E = q.natDegree := IntermediateField.adjoin.finrank hint
    have key : β ^ q.natDegree = (Algebra.norm K γ) ^ N := by
      rw [← hd, ← Algebra.norm_algebraMap (S := E) β, ← hγN, map_pow]
    have hn0 : Algebra.norm K γ ≠ 0 := Algebra.norm_ne_zero_iff.mpr hγ0
    have hunits : (Units.mk0 β hβ) ^ q.natDegree = (Units.mk0 (Algebra.norm K γ) hn0) ^ N := by
      ext
      simp [key]
    have hφeq : (q.natDegree : ℤ) * Multiplicative.toAdd (φ (Units.mk0 β hβ)) =
        (N : ℤ) * Multiplicative.toAdd (φ (Units.mk0 (Algebra.norm K γ) hn0)) := by
      have h2 := congrArg (fun u => Multiplicative.toAdd (φ u)) hunits
      simp only [map_pow, toAdd_pow] at h2
      exact h2
    have hdvdZ : (N : ℤ) ∣ (q.natDegree : ℤ) * Multiplicative.toAdd (φ (Units.mk0 β hβ)) :=
      Dvd.intro _ hφeq.symm
    have hdvdN : N ∣ q.natDegree * (Multiplicative.toAdd (φ (Units.mk0 β hβ))).natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hdvdZ
      simpa [Int.natAbs_mul, Int.natAbs_natCast] using this
    have hdvd : N ∣ q.natDegree := hφ.symm.dvd_of_dvd_mul_right hdvdN
    have hle : q.natDegree ≤ N := hPdeg ▸ natDegree_le_of_dvd hqdvd hPmonic.ne_zero
    have heq : q.natDegree = N := le_antisymm hle (Nat.le_of_dvd (minpoly.natDegree_pos hint) hdvd)
    have hqP : P = q := eq_of_monic_of_dvd_of_natDegree_le hqmonic hPmonic hqdvd (by rw [hPdeg, heq])
    rwa [hqP]


-- created on 2026-10-23
