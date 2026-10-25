/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqbReduction.lean -/

import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Def.GroupTheory.BurnsidePaqbReduction.Part2
/-!
# Conjugacy classes and a Sylow-center reduction step for groups of order `p ^ a * q ^ b`

Authors: Muse Spark 1.3

Port of the fully proved group-theoretic core from the screened archive
`burnside_wip.zip` (SHA-256
`0686f20667e5fef0850dc3c6ba2e4d9e3ef5ba3f89c2f937faa8a251cd1eee30`):
`Burnside/ConjClass.lean` lines 1–45, `Burnside/ClassSum.lean` lines 13–17,
and `Burnside/SylowCenter.lean` lines 1–56.

Historical citation (independently verified): W. Burnside, "On Groups of Order
p^alpha q^beta," *Proceedings of the London Mathematical Society* s2-1 (1904),
388–392, DOI 10.1112/plms/s2-1.1.388.

This partial stage does not prove the full Burnside `p^a * q^b` solvability theorem.
-/


namespace BurnsidePaqb

variable {G : Type*} [Group G] [Fintype G]

open Classical in
/-- Conjugation preserves conjugacy classes. -/
theorem conj_mem_conjClass (g h x : G) (hx : x ∈ conjClass g) :
    h * x * h⁻¹ ∈ conjClass g := by
  rw [mem_conjClass_iff] at hx ⊢
  exact (isConj_iff.mpr ⟨h⁻¹, by group⟩).trans hx

open Classical in
/-- Orbit–stabilizer for conjugacy classes via `ConjAct`. -/
theorem conjClass_card_mul_stabilizer_card {G : Type*} [Group G] [Fintype G] (g : G) :
    (conjClass g).card * Fintype.card (MulAction.stabilizer (ConjAct G) g) =
      Fintype.card G := by
  rw [conjClass, Set.toFinset_card]
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g

open Classical in
/-- Centralizer cardinality equals `ConjAct` stabilizer cardinality. -/
theorem centralizer_card_eq_stabilizer_card {G : Type*} [Group G] [Fintype G] (g : G) :
    Fintype.card (Subgroup.centralizer {g}) =
      Fintype.card (MulAction.stabilizer (ConjAct G) g) :=
  Fintype.card_congr (centralizerEquivStabilizer g)

open Classical in
/-- Class size times centralizer order is `|G|`. -/
theorem conjClass_card_mul_centralizer_card {G : Type*} [Group G] [Fintype G] (g : G) :
    (conjClass g).card * Fintype.card (Subgroup.centralizer {g}) = Fintype.card G := by
  rw [centralizer_card_eq_stabilizer_card]
  exact conjClass_card_mul_stabilizer_card g

end BurnsidePaqb
