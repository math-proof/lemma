import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Submodule_stableLine_fixed_or_cofixed_of_absorbing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Submodule_stableLine_fixed_or_cofixed_of_absorbing.lean)
-/
@[path]
private lemma main
  [SMul G V]
  {p : ℕ} [Fact p.Prime] [AddCommGroup V] [Module (ZMod p) V]
  (S : Set G)
  (N M : Submodule (ZMod p) V)
  -- given
  (hV : Nat.card V = p ^ 2)
  (hN : ∀ g ∈ S, ∀ x ∈ N, g • x ∈ N)
  (hbot : N ≠ ⊥)
  (htop : N ≠ ⊤)
  (hM : M ≠ ⊤)
  (habs : ∀ g ∈ S, ∀ y : V, g • y - y ∈ M) :
  -- imply
  (∀ g ∈ S, ∀ x ∈ N, g • x = x) ∨ (∀ g ∈ S, ∀ y : V, g • y - y ∈ N) := by
  -- proof
  classical
  have hp : p.Prime := Fact.out
  let _ : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; apply pow_ne_zero _ hp.ne_zero)
  let _ : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod p) V = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [Nat.card_zmod, hV] at h
    apply (Nat.pow_right_injective hp.two_le h).symm
  have hN1 : Module.finrank (ZMod p) N = 1 := by
    have hlt : Module.finrank (ZMod p) N < Module.finrank (ZMod p) V := Submodule.finrank_lt htop
    have hne : Module.finrank (ZMod p) N ≠ 0 := by
      rwa [Ne, Submodule.finrank_eq_zero]
    omega
  if hle : N ≤ M then
    right
    have hMlt : Module.finrank (ZMod p) M < Module.finrank (ZMod p) V := Submodule.finrank_lt hM
    have hMN : N = M := Submodule.eq_of_le_of_finrank_le hle (by omega)
    intro g hg y
    rw [hMN]
    apply habs g hg y
  else
    left
    have hinf : N ⊓ M = ⊥ := by
      by_contra hne
      let I : Submodule (ZMod p) V := N ⊓ M
      have hne' : Module.finrank (ZMod p) I ≠ 0 := by
        rwa [Ne, Submodule.finrank_eq_zero]
      have hlefin : Module.finrank (ZMod p) I ≤ Module.finrank (ZMod p) N := by
        simpa [I] using Submodule.finrank_mono (inf_le_left : N ⊓ M ≤ N)
      have heq : I = N := by
        apply Submodule.eq_of_le_of_finrank_le
        · apply inf_le_left
        · omega
      have heq' : N ⊓ M = N := by
        simpa [I] using heq
      refine hle (heq' ▸ inf_le_right)
    intro g hg x hx
    have hmem : g • x - x ∈ N ⊓ M := ⟨N.sub_mem (hN g hg x hx) hx, habs g hg x⟩
    rw [hinf, Submodule.mem_bot] at hmem
    apply sub_eq_zero.mp hmem


-- created on 2026-10-20
