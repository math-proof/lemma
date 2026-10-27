import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Subgroup_nonempty_quotient_zpowers_mulEquiv_of_forall_apply_mem_iff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Subgroup_nonempty_quotient_zpowers_mulEquiv_of_forall_apply_mem_iff.lean)
-/
@[path]
private lemma main
  [CommGroup U] [Group G] [Finite U]
  (Ψ : MonoidHom U G)
  (c : U)
  (H : Subgroup U)
  (I : Subgroup G)
  -- given
  (hΨ : Function.Surjective Ψ)
  (hc : Ψ c = 1)
  (hcard : Nat.card G = (Subgroup.zpowers c).index)
  (hcH : c ∈ H)
  (hI : ∀ u : U, Ψ u ∈ I ↔ u ∈ H) :
  -- imply
  Nonempty (MulEquiv (↥H ⧸ Subgroup.zpowers (Subtype.mk c hcH)) ↥I) := by
  -- proof
  classical
  have hle : Subgroup.zpowers c ≤ Ψ.ker := by
    rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
    apply hc
  have hidx : Ψ.ker.index = (Subgroup.zpowers c).index := by
    rw [← hcard, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hΨ, Subgroup.card_top]
  have hker : Ψ.ker = Subgroup.zpowers c := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hle
    have h1 := Ψ.ker.card_mul_index
    have h2 := (Subgroup.zpowers c).card_mul_index
    have hne : (Subgroup.zpowers c).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hidx] at h1
    let Zc := Subgroup.zpowers c
    have : Nat.card ↥Ψ.ker = Nat.card ↥Zc :=
      Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (h1.trans h2.symm)
    apply this.le
  let ψH : MonoidHom ↥H ↥I := (Ψ.domRestrict H).codRestrict I (fun h => (hI h).mpr h.2)
  have hψH : ∀ h : ↥H, ((ψH h : ↥I) : G) = Ψ (h : U) := fun _ => rfl
  have hsurj : Function.Surjective ψH := by
    intro i
    obtain ⟨u, hu⟩ := hΨ (i : G)
    have huH : u ∈ H := (hI u).mp (by rw [hu]; apply i.2)
    refine ⟨Subtype.mk u huH, Subtype.ext (by rw [hψH]; apply hu)⟩
  have hkerH : ψH.ker = Subgroup.zpowers (Subtype.mk c hcH) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_zpowers_iff]
    constructor
    ·
      intro hx
      have hxU : (x : U) ∈ Ψ.ker := by
        rw [MonoidHom.mem_ker, ← hψH, hx]
        rfl
      rw [hker, Subgroup.mem_zpowers_iff] at hxU
      obtain ⟨k, hk⟩ := hxU
      refine ⟨k, Subtype.ext (by rw [SubgroupClass.coe_zpow]; apply hk)⟩
    ·
      rintro ⟨k, hk⟩
      apply Subtype.ext
      rw [hψH]
      have : ((Subtype.mk c hcH : ↥H) ^ k : ↥H) = x := hk
      rw [← this, SubgroupClass.coe_zpow, map_zpow, hc, one_zpow]
      rfl
  refine ⟨MulEquiv.trans (QuotientGroup.quotientMulEquivOfEq hkerH.symm) (QuotientGroup.quotientKerEquivOfSurjective ψH hsurj)⟩


-- created on 2026-10-20
