import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false


/--
[CerednikDrinfeld_FormalOmega_ringHom_ext_of_isNilpotent_natCast](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_FormalOmega_ringHom_ext_of_isNilpotent_natCast.lean)
-/
@[path]
private lemma main
  {r : ℕ} [Fact r.Prime]
  (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
  (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
  (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
  (C : Type) [CommRing C] (hC : IsNilpotent ((r : ℕ) : C))
  (f g : RingHom 𝒪 C) :
  -- imply
  f = g := by
  -- proof
  classical
  have hr : (r : ℕ).Prime := Fact.out
  have hrI : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := by
    rw [← hunr]
    apply Ideal.mem_span_singleton_self _
  have hI_ne_top : Ideal.span {π} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    apply hπ.not_isUnit
  let _ : Nontrivial (𝒪 ⧸ Ideal.span {π}) := ⟨⟨0, 1, Ideal.Quotient.zero_ne_one_iff.2 hI_ne_top⟩⟩
  let hchar : CharP (𝒪 ⧸ Ideal.span {π}) r := by
    refine (CharP.charP_iff_prime_eq_zero hr).2 ?_
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {π})), Ideal.Quotient.eq_zero_iff_mem]
    apply hrI
  have hcard0 : Nat.card (𝒪 ⧸ Ideal.span {π}) ≠ 0 := by
    rw [hres]
    apply hr.ne_zero
  let _ : Finite (𝒪 ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero hcard0
  let _ : Fintype (𝒪 ⧸ Ideal.span {π}) := Fintype.ofFinite _
  have hbij : Function.Bijective (ZMod.castHom (dvd_refl r) (𝒪 ⧸ Ideal.span {π})) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨ZMod.castHom_injective (𝒪 ⧸ Ideal.span {π}), ?_⟩
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hres]
  let _ : NeZero r := ⟨hr.ne_zero⟩
  have digit : ∀ x : 𝒪, ∃ (a : ℕ) (y : 𝒪), x = a + (r : 𝒪) * y := by
    intro x
    obtain ⟨z, hz⟩ := hbij.2 (Ideal.Quotient.mk (Ideal.span {π}) x)
    refine ⟨z.val, ?_⟩
    have hx : x - (z.val : 𝒪) ∈ Ideal.span {π} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_natCast, ← hz, ZMod.natCast_val, ZMod.castHom_apply, sub_self]
    rw [← hunr, Ideal.mem_span_singleton'] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, ?_⟩
    rw [mul_comm] at hy
    rw [hy]
    ring
  have digits : ∀ (N : ℕ) (x : 𝒪), ∃ (n : ℕ) (y : 𝒪), x = n + (r : 𝒪) ^ N * y := by
    intro N
    induction N with
    | zero =>
      intro x
      refine ⟨0, x, ?_⟩
      simp
    | succ N ih =>
      intro x
      obtain ⟨a, y, hx⟩ := digit x
      obtain ⟨n, z, hy⟩ := ih y
      refine ⟨a + r * n, z, ?_⟩
      rw [hx, hy]
      push_cast
      ring
  obtain ⟨N, hN⟩ := hC
  apply RingHom.ext
  intro x
  obtain ⟨n, y, rfl⟩ := digits N x
  simp [map_add, map_natCast, map_mul, map_pow, hN, zero_mul, add_zero]


-- created on 2026-10-20
