import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[PowerSeries_card_eq_of_isUnit_mul_eq_prod_X_sub_C_of_map_residue_eq_mul_X_pow](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PowerSeries_card_eq_of_isUnit_mul_eq_prod_X_sub_C_of_map_residue_eq_mul_X_pow.lean)
-/
@[path]
private lemma main
  {T : Type u} [CommRing T] [IsLocalRing T]
  (S : Finset ι)
  (z : ι → T)
  (f u : PowerSeries T)
  (N : ℕ)
  -- given
  (hz : ∀ i ∈ S, z i ∈ maximalIdeal T)
  (hu : IsUnit u)
  (hf : ∃ v : PowerSeries (ResidueField T), IsUnit v ∧ PowerSeries.map (residue T) f = v * PowerSeries.X ^ N)
  (h : u * f = ∏ i ∈ S, (PowerSeries.X - PowerSeries.C (z i))) :
  -- imply
  S.card = N := by
  -- proof
  classical
  obtain ⟨v, hv, hfv⟩ := hf
  have hred := congrArg (PowerSeries.map (residue T)) h
  rw [map_mul, hfv, map_prod] at hred
  have hfac : ∀ i ∈ S, PowerSeries.map (residue T) (PowerSeries.X - PowerSeries.C (z i)) = PowerSeries.X := by
    intro i hi
    rw [map_sub, PowerSeries.map_X, PowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff _).mpr (hz i hi), map_zero, sub_zero]
  rw [Finset.prod_congr rfl hfac, Finset.prod_const, ← mul_assoc] at hred
  set w : PowerSeries (ResidueField T) := PowerSeries.map (residue T) u * v with hw
  have hwu : IsUnit w := (hu.map _).mul hv
  have hw0 : PowerSeries.constantCoeff w ≠ 0 := by
    intro h0
    have := PowerSeries.isUnit_iff_constantCoeff.mp hwu
    rw [h0] at this
    apply not_isUnit_zero this
  have hc := congrArg (PowerSeries.coeff N) hred
  rw [PowerSeries.coeff_mul_X_pow', ite_eq_left le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_X_pow] at hc
  by_contra hne
  rw [ite_eq_right (fun h => hne h.symm)] at hc
  apply hw0 hc


-- created on 2026-10-20
