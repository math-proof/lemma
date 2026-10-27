import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[ValuationSubring_algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat.lean)
-/
@[path]
private lemma main
  [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
  (A : ValuationSubring K)
  (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) (ResidueField ↥A)] :
  -- imply
  Algebra.IsAlgebraic (ZMod p) (ResidueField ↥A) := by
  -- proof
  classical
  have hp : p.Prime := Fact.out
  let _ : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  refine ⟨fun r => ?_⟩
  obtain ⟨a, rfl⟩ := residue_surjective r
  have ha : IsAlgebraic ℤ ((a : ↥A) : K) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨P, hP0, hPa⟩ := ha
  have hQprim : P.primPart.IsPrimitive := P.isPrimitive_primPart
  have hQa : Polynomial.aeval ((a : ↥A) : K) P.primPart = 0 := Polynomial.aeval_primPart_eq_zero hP0 hPa
  have hQaA : Polynomial.aeval (a : ↥A) P.primPart = 0 := by
    have h1 : Polynomial.aeval (algebraMap ↥A K a) P.primPart = algebraMap ↥A K (Polynomial.aeval a P.primPart) :=
      Polynomial.aeval_algebraMap_apply K a P.primPart
    apply (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective ↥A K)).mp
    ·
      rw [← h1]
      apply hQa
  have hres : Polynomial.aeval (residue ↥A a) (P.primPart.map (algebraMap ℤ (ZMod p))) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      RingHom.ext_int ((algebraMap (ZMod p) (ResidueField ↥A)).comp (algebraMap ℤ (ZMod p))) (algebraMap ℤ _),
      ← Polynomial.aeval_def]
    have := Polynomial.aeval_algHom_apply ((residue ↥A).toIntAlgHom) a P.primPart
    rw [RingHom.toIntAlgHom_apply] at this
    apply this.trans (by rw [hQaA, map_zero])
  have hne : P.primPart.map (algebraMap ℤ (ZMod p)) ≠ 0 := by
    intro h0
    have hdvd : Polynomial.C (p : ℤ) ∣ P.primPart := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro n
      have hn := congrArg (fun q => q.coeff n) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, algebraMap_int_eq, Int.coe_castRingHom] at hn
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn
    have hu := hQprim (p : ℤ) hdvd
    rw [Int.isUnit_iff] at hu
    have h2 := hp.two_le
    omega
  refine ⟨P.primPart.map (algebraMap ℤ (ZMod p)), hne, hres⟩


-- created on 2026-10-20
