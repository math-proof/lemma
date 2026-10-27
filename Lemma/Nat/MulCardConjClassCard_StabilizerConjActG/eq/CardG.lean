import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.GroupTheory.BurnsidePaqbReduction.Part2
open BurnsidePaqb
open Classical


namespace Definitions
end Definitions
namespace BurnsidePaqb

/--
[conjClass_card_mul_stabilizer_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqbReduction.lean)
-/
@[path]
private lemma conjClass_card_mul_stabilizer_card_eq
  [Group G] [Fintype G]
  {g : G} :
-- imply
  (conjClass g).card * Fintype.card (MulAction.stabilizer (ConjAct G) g) =
    Fintype.card G := by
-- proof
  classical
  rw [conjClass, Set.toFinset_card]
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g

end BurnsidePaqb

namespace BurnsidePaqb

/--
[centralizer_card_eq_stabilizer_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqbReduction.lean)
-/
@[path]
private lemma centralizer_card_eq_stabilizer_card_eq
  [Group G] [Fintype G]
  {g : G} :
-- imply
  Fintype.card (Subgroup.centralizer {g}) =
    Fintype.card (MulAction.stabilizer (ConjAct G) g) :=
-- proof
  Fintype.card_congr (centralizerEquivStabilizer g)

end BurnsidePaqb

namespace BurnsidePaqb

/--
[conjClass_card_mul_centralizer_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqbReduction.lean)
-/
@[path]
private lemma conjClass_card_mul_centralizer_card_eq
  [Group G] [Fintype G]
  {g : G} :
-- imply
  (conjClass g).card * Fintype.card (Subgroup.centralizer {g}) = Fintype.card G := by
-- proof
  rw [centralizer_card_eq_stabilizer_card_eq]
  exact conjClass_card_mul_stabilizer_card_eq (g := g)

end BurnsidePaqb

namespace BurnsidePaqb

/--
[exists_ne_one_class_prime_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqbReduction.lean)
-/
@[path]
private lemma exists_ne_one_class_prime_pow_eq
  [Group G] [Fintype G]
  {p q a b : ℕ}
-- given
  (hp : p.Prime)
  (hq : q.Prime)
  (hcard : Fintype.card G = p ^ a * q ^ b)
  (hb : 1 ≤ b) :
-- imply
  ∃ g : G, g ≠ 1 ∧ ∃ k ≤ a, (conjClass g).card = p ^ k := by
-- proof
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have hqdvd : q ^ b ∣ Nat.card G := by
    rw [Nat.card_eq_fintype_card, hcard]
    exact ⟨p ^ a, by ring⟩
  classical
  obtain ⟨H, hHcard⟩ := Sylow.exists_subgroup_card_pow_prime q hqdvd
  have : Fintype H := inferInstance
  have hHQ : IsPGroup q H := IsPGroup.of_card hHcard
  have hcardH : 1 < Fintype.card H := by
    rw [← Nat.card_eq_fintype_card, hHcard]
    exact one_lt_pow₀ hq.one_lt (by omega)
  have : Nontrivial H := Fintype.one_lt_card_iff_nontrivial.mp hcardH
  have hnt := IsPGroup.center_nontrivial hHQ
  obtain ⟨gH, hgH⟩ := exists_ne (1 : Subgroup.center H)
  refine ⟨((gH : H) : G), ?_, ?_⟩
  ·
    intro hcon
    exact hgH (Subtype.ext (Subtype.ext hcon))
  ·
    have hle : H ≤ Subgroup.centralizer {((gH : H) : G)} := by
      intro h hh
      rw [Subgroup.mem_centralizer_iff]
      simp only [Set.mem_singleton_iff, forall_eq]
      have hmem := Subgroup.mem_center_iff.mp gH.property ⟨h, hh⟩
      have hcoe := congrArg (fun x : H => (x : G)) hmem
      rwa [Subgroup.coe_mul, Subgroup.coe_mul, eq_comm] at hcoe
    set g : G := ((gH : H) : G) with hg
    have hdvd : q ^ b ∣ Fintype.card (Subgroup.centralizer {g}) := by
      have h1 : Nat.card H ∣ Nat.card (Subgroup.centralizer {g}) :=
        Subgroup.card_dvd_of_le hle
      rw [hHcard] at h1
      rwa [Nat.card_eq_fintype_card] at h1
    have hclass := conjClass_card_mul_centralizer_card_eq (g := g)
    rw [hcard] at hclass
    obtain ⟨t, ht⟩ := hdvd
    refine (Nat.dvd_prime_pow hp).mp ⟨t, ?_⟩
    refine (mul_right_cancel₀ (pow_ne_zero b hq.ne_zero) ?_).symm
    calc
      _ = (conjClass g).card * (q ^ b * t) := by ring
      _ = (conjClass g).card * Fintype.card (Subgroup.centralizer {g}) := by rw [ht]
      _ = p ^ a * q ^ b := hclass

end BurnsidePaqb

/--
[mem_conjClass_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqbReduction.lean)
-/
@[path]
private lemma mem_conjClass_iff_eq
  [Group G] [Fintype G]
  {g h : G} :
-- imply
  h ∈ conjClass g ↔ IsConj h g := by
-- proof
  apply BurnsidePaqb.mem_conjClass_iff

/--
[conj_mem_conjClass](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqbReduction.lean)
-/
@[path]
private lemma conj_mem_conjClass_eq
  [Group G] [Fintype G]
  {g h x : G}
-- given
  (hx : x ∈ conjClass g) :
-- imply
  h * x * h⁻¹ ∈ conjClass g := by
-- proof
  apply BurnsidePaqb.conj_mem_conjClass g h x hx


-- created on 2026-10-24
