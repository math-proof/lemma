import Mathlib
import sympy.Basic


/--
[card_add_mul_card_sub_one_eq_card_orbits_mul_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GroupAction/UniformFixedPoints.lean)
-/
@[path]
private lemma main
  (G X : Type*) [Group G] [MulAction G X] [Finite G] [Finite X]
  (c : ℕ)
-- given
  (hfixed : ∀ g : G, g ≠ 1 → Nat.card (MulAction.fixedBy X g) = c) :
-- imply
  Nat.card X + c * (Nat.card G - 1) =
    Nat.card (MulAction.orbitRel.Quotient G X) * Nat.card G := by
-- proof
  classical
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite X
  let _ (g : G) := Fintype.ofFinite (MulAction.fixedBy X g)
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient G X)
  simp only [Nat.card_eq_fintype_card] at hfixed ⊢
  rw [← MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group]
  symm
  have hsum :
    (∑ g ∈ (Finset.univ : Finset G).erase 1,
      Fintype.card (MulAction.fixedBy X g)) =
      ∑ _ ∈ (Finset.univ : Finset G).erase 1, c := by
    apply Finset.sum_congr rfl
    intro g hg
    exact hfixed g (Finset.ne_of_mem_erase hg)
  have h1 :
    (∑ g : G, Fintype.card (MulAction.fixedBy X g)) =
      (∑ g ∈ (Finset.univ : Finset G).erase 1,
        Fintype.card (MulAction.fixedBy X g)) +
        Fintype.card (MulAction.fixedBy X (1 : G)) := by
    simpa using (Finset.sum_erase_add (Finset.univ : Finset G)
      (fun g : G => Fintype.card (MulAction.fixedBy X g)) (Finset.mem_univ 1)).symm
  rw [h1, hsum]
  simp [MulAction.fixedBy_one_eq_univ, Nat.mul_comm]
  omega


-- created on 2026-10-20
-- updated on 2026-10-24
