import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.GroupCounts.Part8
open GroupCounts
open scoped Classical


namespace GroupCounts

/--
[G₂₄_inv_eq_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
lemma G₂₄_inv_eq_self (a : G₂₄) : a⁻¹ = a := by
  fin_cases a <;> decide

end GroupCounts

namespace GroupCounts

/--
[subgroupToFinset₂₄_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
lemma subgroupToFinset₂₄_mem (H : Subgroup G₂₄) (g : G₂₄) :
  g ∈ subgroupToFinset₂₄ H ↔ g ∈ H := by
  unfold subgroupToFinset₂₄; simp [Finset.mem_filter]
set_option maxHeartbeats 400000 in

end GroupCounts

namespace GroupCounts

/--
[subgroupToFinset₂₄_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
lemma subgroupToFinset₂₄_card (H : Subgroup G₂₄) :
  (subgroupToFinset₂₄ H).card = Nat.card H := by
  rw [Nat.card_eq_fintype_card, subgroupToFinset₂₄, Fintype.card_of_subtype]
  intro x; simp

end GroupCounts

namespace GroupCounts

/--
[natcard_G₂₄](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
lemma natcard_G₂₄ : Nat.card G₂₄ = 16 := by
  rw [Nat.card_eq_fintype_card]; decide

end GroupCounts

namespace GroupCounts

/--
[subgroupToFinset₂₄_is_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
lemma subgroupToFinset₂₄_is_carrier (H : Subgroup G₂₄) :
  (1 : G₂₄) ∈ subgroupToFinset₂₄ H ∧
  (∀ a ∈ subgroupToFinset₂₄ H, ∀ b ∈ subgroupToFinset₂₄ H,
    a * b ∈ subgroupToFinset₂₄ H) := by
  constructor
  · rw [subgroupToFinset₂₄_mem]; exact H.one_mem
  · intro a ha b hb
    rw [subgroupToFinset₂₄_mem] at ha hb ⊢; exact H.mul_mem ha hb

end GroupCounts

namespace GroupCounts

/--
[round_trip_finset₂₄](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
lemma round_trip_finset₂₄ (s : Finset G₂₄) (h1 : (1 : G₂₄) ∈ s)
  (hmul : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) :
  subgroupToFinset₂₄ (finsetToSubgroup₂₄ s h1 hmul) = s := by
  ext g; rw [subgroupToFinset₂₄_mem]; simp [finsetToSubgroup₂₄]

end GroupCounts

namespace GroupCounts

/--
[round_trip_subgroup₂₄](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
lemma round_trip_subgroup₂₄ (H : Subgroup G₂₄) :
  finsetToSubgroup₂₄ (subgroupToFinset₂₄ H)
    (subgroupToFinset₂₄_is_carrier H).1
    (subgroupToFinset₂₄_is_carrier H).2 = H := by
  apply Subgroup.ext; intro g
  simp [finsetToSubgroup₂₄, subgroupToFinset₂₄_mem]

end GroupCounts

namespace GroupCounts

/--
[subgroupToFinset₄₃_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
lemma subgroupToFinset₄₃_mem (H : Subgroup G₄₃) (g : G₄₃) :
  g ∈ subgroupToFinset₄₃ H ↔ g ∈ H := by
  unfold subgroupToFinset₄₃; simp [Finset.mem_filter]

end GroupCounts

namespace GroupCounts

/--
[subgroupToFinset₄₃_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
lemma subgroupToFinset₄₃_injective :
  Function.Injective subgroupToFinset₄₃ := by
  intro H₁ H₂ h; apply Subgroup.ext; intro g
  rw [← subgroupToFinset₄₃_mem H₁, ← subgroupToFinset₄₃_mem H₂, h]
set_option maxHeartbeats 400000 in

end GroupCounts

namespace GroupCounts

/--
[natcard_G₄₃](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
lemma natcard_G₄₃ : Nat.card G₄₃ = 64 := by
  rw [Nat.card_eq_fintype_card]; decide

end GroupCounts

/--
[G](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma G_eq
  {a : G₂₄} :
-- imply
  a⁻¹ = a := by
-- proof
  apply GroupCounts.G a

/--
[subgroupToFinset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma subgroupToFinset_eq
  {H : Subgroup G₂₄}
  {g : G₂₄} :
-- imply
  g ∈ subgroupToFinset₂₄ H ↔ g ∈ H := by
-- proof
  apply GroupCounts.subgroupToFinset H g

/--
[subgroupToFinset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma subgroupToFinset_eq_2
  {H : Subgroup G₂₄} :
-- imply
  (subgroupToFinset₂₄ H).card = Nat.card H := by
-- proof
  apply GroupCounts.subgroupToFinset H

/--
[natcard_G](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma natcard_G_eq :
-- imply
  Nat.card G₂₄ = 16 := by
-- proof
  apply GroupCounts.natcard_G

/--
[index_eq_two_iff_card_eq_eight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma index_eq_two_iff_card_eq_eight_eq
  {H : Subgroup G₂₄} :
-- imply
  H.index = 2 ↔ Nat.card H = 8 := by
-- proof
  apply GroupCounts.index_eq_two_iff_card_eq_eight H

/--
[subgroupToFinset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma subgroupToFinset_eq_3
  {H : Subgroup G₂₄} :
-- imply
  (1 : G₂₄) ∈ subgroupToFinset₂₄ H ∧ (∀ a ∈ subgroupToFinset₂₄ H, ∀ b ∈ subgroupToFinset₂₄ H, a * b ∈ subgroupToFinset₂₄ H) := by
-- proof
  apply GroupCounts.subgroupToFinset H

/--
[round_trip_finset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma round_trip_finset_eq
  {s : Finset G₂₄}
-- given
  (h0 : (1 : G₂₄) ∈ s)
  (hmul : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) :
-- imply
  subgroupToFinset₂₄ (finsetToSubgroup₂₄ s h0 hmul) = s := by
-- proof
  apply GroupCounts.round_trip_finset s h0 hmul

/--
[round_trip_subgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma round_trip_subgroup_eq
  {H : Subgroup G₂₄} :
-- imply
  finsetToSubgroup₂₄ (subgroupToFinset₂₄ H) (subgroupToFinset₂₄_is_carrier H).1 (subgroupToFinset₂₄_is_carrier H).2 = H := by
-- proof
  apply GroupCounts.round_trip_subgroup H

/--
[subgroupCarriersIdx2_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma subgroupCarriersIdx2_card_eq :
-- imply
  subgroupCarriersIdx2.card = 15 := by
-- proof
  apply GroupCounts.subgroupCarriersIdx2_card

/--
[mem_subgroupCarriersIdx2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma mem_subgroupCarriersIdx2_eq
  {s : Finset G₂₄} :
-- imply
  s ∈ subgroupCarriersIdx2 ↔ (1 : G₂₄) ∈ s ∧ (∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) ∧ s.card = 8 := by
-- proof
  apply GroupCounts.mem_subgroupCarriersIdx2 s

/--
[Z2Z4_index2_count](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma Z2Z4_index2_count_eq :
-- imply
  Nat.card {H : Subgroup (Multiplicative (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)) // H.index = 2} = 15 := by
-- proof
  apply GroupCounts.Z2Z4_index2_count

/--
[mem_ker_mulHomTriple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma mem_ker_mulHomTriple_eq
  {a b c : ZMod 4}
  {g : G₄₃} :
-- imply
  g ∈ (mulHomTriple a b c).ker ↔ a * g.toAdd.1 + b * g.toAdd.2.1 + c * g.toAdd.2.2 = 0 := by
-- proof
  apply GroupCounts.mem_ker_mulHomTriple a b c g

/--
[mulHomTriple_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma mulHomTriple_surjective_eq
  {a b c : ZMod 4}
-- given
  (h : isSurjTriple a b c) :
-- imply
  Function.Surjective (mulHomTriple a b c) := by
-- proof
  apply GroupCounts.mulHomTriple_surjective a b c h

/--
[mulHomTriple_ker_index](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma mulHomTriple_ker_index_eq
  {a b c : ZMod 4}
-- given
  (h : isSurjTriple a b c) :
-- imply
  (mulHomTriple a b c).ker.index = 4 := by
-- proof
  apply GroupCounts.mulHomTriple_ker_index a b c h

/--
[mulHomTriple_ker_isCyclic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma mulHomTriple_ker_isCyclic_eq
  {a b c : ZMod 4}
-- given
  (h : isSurjTriple a b c) :
-- imply
  IsCyclic (G₄₃ ⧸ (mulHomTriple a b c).ker) := by
-- proof
  apply GroupCounts.mulHomTriple_ker_isCyclic a b c h

/--
[addHom_eq_triple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma addHom_eq_triple_eq
  {f : (ZMod 4 × ZMod 4 × ZMod 4) →+ ZMod 4}
  {x y z : ZMod 4} :
-- imply
  f (x, y, z) = f (1, 0, 0) * x + f (0, 1, 0) * y + f (0, 0, 1) * z := by
-- proof
  apply GroupCounts.addHom_eq_triple f x y z

/--
[mulHom_eq_triple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma mulHom_eq_triple_eq
  {f : G₄₃ →* Multiplicative (ZMod 4)} :
-- imply
  ∃ a b c : ZMod 4, ∀ g : G₄₃, f g = mulHomTriple a b c g := by
-- proof
  apply GroupCounts.mulHom_eq_triple f

/--
[subgroupToFinset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma subgroupToFinset_eq_4
  {H : Subgroup G₄₃}
  {g : G₄₃} :
-- imply
  g ∈ subgroupToFinset₄₃ H ↔ g ∈ H := by
-- proof
  apply GroupCounts.subgroupToFinset H g

/--
[subgroupToFinset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma subgroupToFinset_eq_5 :
-- imply
  Function.Injective subgroupToFinset₄₃ := by
-- proof
  apply GroupCounts.subgroupToFinset

/--
[natcard_G](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma natcard_G_eq_2 :
-- imply
  Nat.card G₄₃ = 64 := by
-- proof
  apply GroupCounts.natcard_G

/--
[surjKernelsMul_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma surjKernelsMul_card_eq :
-- imply
  surjKernelsMul.card = 28 := by
-- proof
  apply GroupCounts.surjKernelsMul_card

/--
[ker_carrier_eq_kerFinsetMul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma ker_carrier_eq_kerFinsetMul_eq
  {a b c : ZMod 4} :
-- imply
  subgroupToFinset₄₃ (mulHomTriple a b c).ker = kerFinsetMul a b c := by
-- proof
  apply GroupCounts.ker_carrier_eq_kerFinsetMul a b c

/--
[ker_carrier_mem_surjKernels](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma ker_carrier_mem_surjKernels_eq
  {a b c : ZMod 4}
-- given
  (h : isSurjTriple a b c) :
-- imply
  subgroupToFinset₄₃ (mulHomTriple a b c).ker ∈ surjKernelsMul := by
-- proof
  apply GroupCounts.ker_carrier_mem_surjKernels a b c h

/--
[carrier_of_cyclic_idx4_in_surjKernels](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma carrier_of_cyclic_idx4_in_surjKernels_eq
  {H : Subgroup G₄₃}
-- given
  (hidx : H.index = 4)
  (hcyc : IsCyclic (G₄₃ ⧸ H)) :
-- imply
  subgroupToFinset₄₃ H ∈ surjKernelsMul := by
-- proof
  apply GroupCounts.carrier_of_cyclic_idx4_in_surjKernels H hidx hcyc

/--
[Z4Z3_cyclic_quartic_count](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean)
-/
@[path]
private lemma Z4Z3_cyclic_quartic_count_eq :
-- imply
  Nat.card {H : Subgroup (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)) // H.index = 4 ∧ IsCyclic (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4) ⧸ H)} = 28 := by
-- proof
  apply GroupCounts.Z4Z3_cyclic_quartic_count


-- created on 2026-10-23
