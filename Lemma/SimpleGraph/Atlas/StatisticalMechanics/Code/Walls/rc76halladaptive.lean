import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc76halladaptive.Part3
open Finset StatMech StatMech.Walls


/--
[swapSet_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean)
-/
@[path]
private lemma swapSet_involutive_eq
  {n : ℕ}
  {L : Finset (Fin n)} :
-- imply
  Function.Involutive (swapSet L) := by
-- proof
  apply StatMech.Walls.swapSet_involutive L

/--
[swapSet_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean)
-/
@[path]
private lemma swapSet_bijective_eq
  {n : ℕ}
  {L : Finset (Fin n)} :
-- imply
  Function.Bijective (swapSet L) := by
-- proof
  apply StatMech.Walls.swapSet_bijective L

/--
[swapSet_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean)
-/
@[path]
private lemma swapSet_off_eq
  {n : ℕ}
  {L : Finset (Fin n)}
  {p : ConfigSpace (Fin n) × ConfigSpace (Fin n)}
  {j : Fin n}
-- given
  (hj : j ∉ L) :
-- imply
  (swapSet L p).1 j = p.1 j ∧ (swapSet L p).2 j = p.2 j := by
-- proof
  apply StatMech.Walls.swapSet_off L p hj

/--
[swapSet_on](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean)
-/
@[path]
private lemma swapSet_on_eq
  {n : ℕ}
  {L : Finset (Fin n)}
  {p : ConfigSpace (Fin n) × ConfigSpace (Fin n)}
  {j : Fin n}
-- given
  (hj : j ∈ L) :
-- imply
  (swapSet L p).1 j = p.2 j ∧ (swapSet L p).2 j = p.1 j := by
-- proof
  apply StatMech.Walls.swapSet_on L p hj

/--
[swapSet_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean)
-/
@[path]
private lemma swapSet_singleton_eq
  {n : ℕ}
  {i : Fin n}
  {p : ConfigSpace (Fin n) × ConfigSpace (Fin n)} :
-- imply
  swapSet {i} p = swapAt i p := by
-- proof
  apply StatMech.Walls.swapSet_singleton i p

/--
[rc76_swapSet_mapsInto_of_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean)
-/
@[path]
private lemma rc76_swapSet_mapsInto_of_witness_eq
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin n))}
  {K L : Finset (Fin n)}
  {ω₁ ω₂ : ConfigSpace (Fin n)}
-- given
  (hKL : Disjoint K L)
  (hA : OccursOn A (K : Set (Fin n)) ω₁)
  (hB : OccursOn B (L : Set (Fin n)) ω₁) :
-- imply
  (swapSet L (ω₁, ω₂)).1 ∈ A ∧ (swapSet L (ω₁, ω₂)).2 ∈ B := by
-- proof
  apply StatMech.Walls.rc76_swapSet_mapsInto_of_witness A B hKL ω₁ ω₂ hA hB

/--
[rc76_swapSet_mapsInto_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean)
-/
@[path]
private lemma rc76_swapSet_mapsInto_singleton_eq
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin n))}
  {K : Finset (Fin n)}
  {i : Fin n}
  {ω₁ ω₂ : ConfigSpace (Fin n)}
-- given
  (hKi : Disjoint K {i})
  (hA : OccursOn A (K : Set (Fin n)) ω₁)
  (hB : OccursOn B ({i} : Finset (Fin n)) ω₁) :
-- imply
  (swapAt i (ω₁, ω₂)).1 ∈ A ∧ (swapAt i (ω₁, ω₂)).2 ∈ B := by
-- proof
  apply StatMech.Walls.rc76_swapSet_mapsInto_singleton A B hKi ω₁ ω₂ hA hB

/--
[rc76_mem_reachNbhd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean)
-/
@[path]
private lemma rc76_mem_reachNbhd_eq
  {n : ℕ}
  {A B : Finset (ConfigSpace (Fin n))}
  {p q : ConfigSpace (Fin n) × ConfigSpace (Fin n)} :
-- imply
  q ∈ rc76_reachNbhd A B p ↔ (q.1 ∈ A ∧ q.2 ∈ B) ∧ ∃ S : Finset (Fin n), swapSet S p = q := by
-- proof
  apply StatMech.Walls.rc76_mem_reachNbhd A B p q

/--
[rc76_hall_iff_plan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean)
-/
@[path]
private lemma rc76_hall_iff_plan_eq
  {n : ℕ}
  {A B : Finset (ConfigSpace (Fin n))}
  {src : Finset (ConfigSpace (Fin n) × ConfigSpace (Fin n))} :
-- imply
  (∀ T : Finset (ConfigSpace (Fin n) × ConfigSpace (Fin n)), T ⊆ src → T.card ≤ (T.biUnion (fun p => rc76_reachNbhd A B p)).card) ↔ ∃ f : (ConfigSpace (Fin n) × ConfigSpace (Fin n)) → (ConfigSpace (Fin n) × ConfigSpace (Fin n)), Set.InjOn f src ∧ ∀ p ∈ src, f p ∈ rc76_reachNbhd A B p := by
-- proof
  apply StatMech.Walls.rc76_hall_iff_plan A B src

/--
[rc76_swapSet_reachable_iff_colType](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean)
-/
@[path]
private lemma rc76_swapSet_reachable_iff_colType_eq
  {n : ℕ}
  {p q : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)} :
-- imply
  (∃ S ∈ (Finset.univ : Finset (Fin 2)).powerset, swapSet S p = q) ↔ rc78_colTypeF q = rc78_colTypeF p := by
-- proof
  apply StatMech.Walls.rc76_swapSet_reachable_iff_colType p q

/--
[rc76_reachNbhdF_eq_rc78_nbhd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean)
-/
@[path]
private lemma rc76_reachNbhdF_eq_rc78_nbhd_eq
  {n : ℕ}
  {A B : Finset (ConfigSpace (Fin 2))}
  {p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)} :
-- imply
  rc76_reachNbhdF A B p = rc78_nbhd A B p := by
-- proof
  apply StatMech.Walls.rc76_reachNbhdF_eq_rc78_nbhd A B p

/--
[rc76_marriage_iff_wall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean)
-/
@[path]
private lemma rc76_marriage_iff_wall_eq
  {n : ℕ} :
-- imply
  ∀ A B : Finset (ConfigSpace (Fin 2)), rc76_marriage A B ↔ rc76_wall A B := by
-- proof
  apply StatMech.Walls.rc76_marriage_iff_wall

/--
[rc76_marriage_binds_at_proper_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean)
-/
@[path]
private lemma rc76_marriage_binds_at_proper_subset_eq
  {n : ℕ} :
-- imply
  ∃ T ∈ (rc76_source rc75_gA rc75_gB).powerset, T.Nonempty ∧ T ≠ rc76_source rc75_gA rc75_gB ∧ (T.biUnion (fun p => rc76_reachNbhdF rc75_gA rc75_gB p)).card < (rc76_source rc75_gA rc75_gB).card := by
-- proof
  apply StatMech.Walls.rc76_marriage_binds_at_proper_subset

/--
[rc76_count_insufficient_arbitrary_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean)
-/
@[path]
private lemma rc76_count_insufficient_arbitrary_source_eq
  {n : ℕ} :
-- imply
  let S₀ : Finset (ConfigSpace (Fin 2)) := {rc75_cfg false true} let A : Finset (ConfigSpace (Fin 2)) := {rc75_cfg true false, rc75_cfg true true} let B : Finset (ConfigSpace (Fin 2)) := Finset.univ let src : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) := S₀ ×ˢ Finset.univ 2 ^ 2 * S₀.card ≤ A.card * B.card ∧ (src.biUnion (fun p => rc76_reachNbhdF A B p)).card < src.card := by
-- proof
  apply StatMech.Walls.rc76_count_insufficient_arbitrary_source


-- created on 2026-10-23
