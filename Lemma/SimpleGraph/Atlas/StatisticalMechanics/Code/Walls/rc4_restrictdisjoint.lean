import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc4_restrictdisjoint
open Finset Set StatMech StatMech.Walls


/--
[rc4_restrict_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_restrictdisjoint.lean)
-/
@[path]
private lemma rc4_restrict_disjoint_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {K L : Finset α}
-- given
  (h : Disjoint K L) :
-- imply
  Disjoint (K ∩ rc4_differSet k) (L ∩ rc4_differSet k) := by
-- proof
  apply StatMech.Walls.rc4_restrict_disjoint k h

/--
[rc4_restrict_disjoint_subtype](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_restrictdisjoint.lean)
-/
@[path]
private lemma rc4_restrict_disjoint_subtype_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {K L : Finset α}
-- given
  (h : Disjoint K L) :
-- imply
  Disjoint (K.subtype (· ∈ rc4_differSet k)) (L.subtype (· ∈ rc4_differSet k)) := by
-- proof
  apply StatMech.Walls.rc4_restrict_disjoint_subtype k h

/--
[rc4_map_subtype_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_restrictdisjoint.lean)
-/
@[path]
private lemma rc4_map_subtype_restrict_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {K : Finset α} :
-- imply
  (K.subtype (· ∈ rc4_differSet k)).map (Function.Embedding.subtype _) = K ∩ rc4_differSet k := by
-- proof
  apply StatMech.Walls.rc4_map_subtype_restrict k K

/--
[rc4_restrict_disjoint_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_restrictdisjoint.lean)
-/
@[path]
private lemma rc4_restrict_disjoint_set_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {K L : Set α}
-- given
  (h : Disjoint K L) :
-- imply
  Disjoint (K ∩ (rc4_differSet k : Set α)) (L ∩ (rc4_differSet k : Set α)) := by
-- proof
  apply StatMech.Walls.rc4_restrict_disjoint_set k h

/--
[rc4_witnesses_restrict_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_restrictdisjoint.lean)
-/
@[path]
private lemma rc4_witnesses_restrict_disjoint_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {A B : Set (ConfigSpace α)}
  {ω : ConfigSpace α}
-- given
  (hω : ω ∈ disjointOccurrence A B) :
-- imply
  ∃ s K L : Finset α, SupportEncodedMinimalWitness A B ω s K L ∧ Disjoint (K ∩ rc4_differSet k) (L ∩ rc4_differSet k) ∧ Disjoint (K.subtype (· ∈ rc4_differSet k)) (L.subtype (· ∈ rc4_differSet k)) := by
-- proof
  apply StatMech.Walls.rc4_witnesses_restrict_disjoint k hω


-- created on 2026-10-23
