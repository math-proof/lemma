import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false


/--
[CerednikDrinfeld_isUnit_natCast_of_not_dvd_of_card_quotient](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_isUnit_natCast_of_not_dvd_of_card_quotient.lean)
-/
@[path]
private lemma main
  {r : ℕ} [Fact r.Prime]
  (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪]
  (π : 𝒪) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
  (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
  (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
  (m : ℕ) (hm : ¬ r ∣ m) :
  -- imply
  IsUnit ((m : ℕ) : 𝒪) := by
  -- proof
  classical
  let _ : IsAdicComplete (Ideal.span {π}) 𝒪 := hcomplete
  have hr : r.Prime := Fact.out
  have hcard0 : Nat.card (𝒪 ⧸ Ideal.span {π}) ≠ 0 := by
    rw [hres]
    apply hr.ne_zero
  have hfin : Finite (𝒪 ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero hcard0
  let _ : Fintype (𝒪 ⧸ Ideal.span {π}) := Fintype.ofFinite _
  have hcard : Fintype.card (𝒪 ⧸ Ideal.span {π}) = r := by
    rw [← Nat.card_eq_fintype_card]
    apply hres
  let e : RingEquiv (ZMod r) (𝒪 ⧸ Ideal.span {π}) := ZMod.ringEquivOfPrime (𝒪 ⧸ Ideal.span {π}) hr hcard
  have hmq : IsUnit ((m : ℕ) : 𝒪 ⧸ Ideal.span {π}) := by
    have h1 : ((m : ℕ) : 𝒪 ⧸ Ideal.span {π}) = e (m : ZMod r) := by
      simp [map_natCast]
    rw [h1]
    refine IsUnit.map e ?_
    refine isUnit_iff_ne_zero.mpr ?_
    intro h
    apply hm ((ZMod.natCast_eq_zero_iff m r).mp h)
  obtain ⟨a, ha⟩ : ∃ a : 𝒪, (m : 𝒪) * a - 1 ∈ Ideal.span {π} := by
    obtain ⟨u, hu⟩ := hmq
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {π}) (↑u⁻¹ : 𝒪 ⧸ Ideal.span {π})
    refine ⟨a, ?_⟩
    rw [← Ideal.Quotient.eq, map_mul, map_one, map_natCast, ha, ← hu, Units.mul_inv]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
  have hjac : π ∈ (⊥ : Ideal 𝒪).jacobson := (IsAdicComplete.le_jacobson_bot (Ideal.span {π})) (Ideal.subset_span (Set.mem_singleton π))
  have hu1 : IsUnit (π * c + 1) := (Ideal.mem_jacobson_bot.mp hjac) c
  have hprod : (m : 𝒪) * a = π * c + 1 := by
    have heq : (m : 𝒪) * a - 1 = c * π := hc.symm
    linear_combination heq
  refine isUnit_of_mul_isUnit_left (y := a) ?_
  rw [hprod]
  apply hu1


-- created on 2026-10-20
