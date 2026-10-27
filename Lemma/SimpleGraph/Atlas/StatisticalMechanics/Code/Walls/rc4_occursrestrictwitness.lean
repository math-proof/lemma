import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc4_occursrestrictwitness.Part5
open Finset StatMech StatMech.Walls


/--
[mem_pocDiffer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_occursrestrictwitness.lean)
-/
@[path]
private lemma mem_pocDiffer_eq
  {k : ConfigSpace α × ConfigSpace α}
  {a : α} :
-- imply
  a ∈ pocDiffer k ↔ k.1 a ≠ k.2 a := by
-- proof
  apply StatMech.Walls.mem_pocDiffer k a

/--
[pocRestrict_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_occursrestrictwitness.lean)
-/
@[path]
private lemma pocRestrict_apply_eq
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α}
  {s : DifferSub k} :
-- imply
  pocRestrict k ω s = ω s.1 := by
-- proof
  apply StatMech.Walls.pocRestrict_apply k ω s

/--
[pocUnrestrict_apply_differ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_occursrestrictwitness.lean)
-/
@[path]
private lemma pocUnrestrict_apply_differ_eq
  {k : ConfigSpace α × ConfigSpace α}
  {σ : ConfigSpace (DifferSub k)}
  {a : α}
-- given
  (h : k.1 a ≠ k.2 a) :
-- imply
  pocUnrestrict k σ a = σ ⟨a, h⟩ := by
-- proof
  apply StatMech.Walls.pocUnrestrict_apply_differ k σ h

/--
[pocUnrestrict_apply_nondiffer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_occursrestrictwitness.lean)
-/
@[path]
private lemma pocUnrestrict_apply_nondiffer_eq
  {k : ConfigSpace α × ConfigSpace α}
  {σ : ConfigSpace (DifferSub k)}
  {a : α}
-- given
  (h : k.1 a = k.2 a) :
-- imply
  pocUnrestrict k σ a = k.1 a := by
-- proof
  apply StatMech.Walls.pocUnrestrict_apply_nondiffer k σ h

/--
[pocRestrict_pocUnrestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_occursrestrictwitness.lean)
-/
@[path]
private lemma pocRestrict_pocUnrestrict_eq
  {k : ConfigSpace α × ConfigSpace α}
  {σ : ConfigSpace (DifferSub k)} :
-- imply
  pocRestrict k (pocUnrestrict k σ) = σ := by
-- proof
  apply StatMech.Walls.pocRestrict_pocUnrestrict k σ

/--
[mem_pocFrozenRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_occursrestrictwitness.lean)
-/
@[path]
private lemma mem_pocFrozenRestrict_eq
  {k : ConfigSpace α × ConfigSpace α}
  {A : Set (ConfigSpace α)}
  {σ : ConfigSpace (DifferSub k)} :
-- imply
  σ ∈ pocFrozenRestrict k A ↔ pocUnrestrict k σ ∈ A := by
-- proof
  apply StatMech.Walls.mem_pocFrozenRestrict k A σ

/--
[mem_pocRestrictWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_occursrestrictwitness.lean)
-/
@[path]
private lemma mem_pocRestrictWitness_eq
  {k : ConfigSpace α × ConfigSpace α}
  {K : Set α}
  {s : DifferSub k} :
-- imply
  s ∈ pocRestrictWitness k K ↔ s.1 ∈ K := by
-- proof
  apply StatMech.Walls.mem_pocRestrictWitness k K s

/--
[rc4_agreeOn_unrestrict_of_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_occursrestrictwitness.lean)
-/
@[path]
private lemma rc4_agreeOn_unrestrict_of_restrict_eq
  {k : ConfigSpace α × ConfigSpace α}
  {K : Set α}
  {ω : ConfigSpace α}
  {σ' : ConfigSpace (DifferSub k)}
-- given
  (hfroz : ∀ a, k.1 a = k.2 a → ω a = k.1 a)
  (hagree : agreeOn (pocRestrictWitness k K) (pocRestrict k ω) σ') :
-- imply
  agreeOn K ω (pocUnrestrict k σ') := by
-- proof
  apply StatMech.Walls.rc4_agreeOn_unrestrict_of_restrict hfroz hagree

/--
[rc4_occurs_restrict_witness_frozen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_occursrestrictwitness.lean)
-/
@[path]
private lemma rc4_occurs_restrict_witness_frozen_eq
  {k : ConfigSpace α × ConfigSpace α}
  {A : Set (ConfigSpace α)}
  {K : Set α}
  {ω : ConfigSpace α}
-- given
  (hfroz : ∀ a, k.1 a = k.2 a → ω a = k.1 a)
  (hocc : OccursOn A K ω) :
-- imply
  OccursOn (pocFrozenRestrict k A) (pocRestrictWitness k K) (pocRestrict k ω) := by
-- proof
  apply StatMech.Walls.rc4_occurs_restrict_witness_frozen hfroz hocc

/--
[rc4_occurs_restrict_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_occursrestrictwitness.lean)
-/
@[path]
private lemma rc4_occurs_restrict_witness_eq
  {k : ConfigSpace α × ConfigSpace α}
  {A : Set (ConfigSpace α)}
  {K : Set α}
  {ω : ConfigSpace α}
-- given
  (hslab : ω ∈ rc2_slab k)
  (hocc : OccursOn A K ω) :
-- imply
  OccursOn (pocFrozenRestrict k A) (pocRestrictWitness k K) (pocRestrict k ω) := by
-- proof
  apply StatMech.Walls.rc4_occurs_restrict_witness hslab hocc

/--
[topKey_differ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_occursrestrictwitness.lean)
-/
@[path]
private lemma topKey_differ_eq
  {a : α} :
-- imply
  (poc_topKey : ConfigSpace α × ConfigSpace α).1 a ≠ poc_topKey.2 a := by
-- proof
  apply StatMech.Walls.topKey_differ a

/--
[pocUnrestrict_pocRestrict_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_occursrestrictwitness.lean)
-/
@[path]
private lemma pocUnrestrict_pocRestrict_top_eq
  {ω : ConfigSpace α} :
-- imply
  pocUnrestrict (poc_topKey : ConfigSpace α × ConfigSpace α) (pocRestrict poc_topKey ω) = ω := by
-- proof
  apply StatMech.Walls.pocUnrestrict_pocRestrict_top ω

/--
[rc4_occurs_restrict_witness_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_occursrestrictwitness.lean)
-/
@[path]
private lemma rc4_occurs_restrict_witness_top_eq
  {A : Set (ConfigSpace α)}
  {K : Set α}
  {ω : ConfigSpace α}
-- given
  (hocc : OccursOn A K ω) :
-- imply
  OccursOn (pocFrozenRestrict (poc_topKey : ConfigSpace α × ConfigSpace α) A) (pocRestrictWitness poc_topKey K) (pocRestrict poc_topKey ω) := by
-- proof
  apply StatMech.Walls.rc4_occurs_restrict_witness_top hocc


-- created on 2026-10-23
