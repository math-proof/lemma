import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc6overlapsplit
open Finset StatMech StatMech.Walls


/--
[rc6_classify_eq_both](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6overlapsplit.lean)
-/
@[path]
private lemma rc6_classify_eq_both_eq
  {K L : Set α}
  {i : α} :
-- imply
  rc6_classify K L i = both ↔ i ∈ K ∧ i ∈ L := by
-- proof
  apply StatMech.Walls.rc6_classify_eq_both i

/--
[rc6_classify_eq_onlyK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6overlapsplit.lean)
-/
@[path]
private lemma rc6_classify_eq_onlyK_eq
  {K L : Set α}
  {i : α} :
-- imply
  rc6_classify K L i = onlyK ↔ i ∈ K ∧ i ∉ L := by
-- proof
  apply StatMech.Walls.rc6_classify_eq_onlyK i

/--
[rc6_classify_eq_onlyL](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6overlapsplit.lean)
-/
@[path]
private lemma rc6_classify_eq_onlyL_eq
  {K L : Set α}
  {i : α} :
-- imply
  rc6_classify K L i = onlyL ↔ i ∉ K ∧ i ∈ L := by
-- proof
  apply StatMech.Walls.rc6_classify_eq_onlyL i

/--
[rc6_classify_eq_neither](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6overlapsplit.lean)
-/
@[path]
private lemma rc6_classify_eq_neither_eq
  {K L : Set α}
  {i : α} :
-- imply
  rc6_classify K L i = neither ↔ i ∉ K ∧ i ∉ L := by
-- proof
  apply StatMech.Walls.rc6_classify_eq_neither i

/--
[rc6_classify_ne_both_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6overlapsplit.lean)
-/
@[path]
private lemma rc6_classify_ne_both_of_disjoint_eq
  {K L : Set α}
  {i : α}
-- given
  (h : Disjoint K L) :
-- imply
  rc6_classify K L i ≠ both := by
-- proof
  apply StatMech.Walls.rc6_classify_ne_both_of_disjoint h i

/--
[rc6_classify_mem_three_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6overlapsplit.lean)
-/
@[path]
private lemma rc6_classify_mem_three_of_disjoint_eq
  {K L : Set α}
  {i : α}
-- given
  (h : Disjoint K L) :
-- imply
  rc6_classify K L i ∈ ({neither, onlyK, onlyL} : Finset WitnessClass) := by
-- proof
  apply StatMech.Walls.rc6_classify_mem_three_of_disjoint h i

/--
[rc6_overlap_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6overlapsplit.lean)
-/
@[path]
private lemma rc6_overlap_trichotomy_eq
  {K L : Set α}
  {i : α}
-- given
  (h : Disjoint K L) :
-- imply
  (i ∈ K ∧ i ∉ L) ∨ (i ∉ K ∧ i ∈ L) ∨ (i ∉ K ∧ i ∉ L) := by
-- proof
  apply StatMech.Walls.rc6_overlap_trichotomy h i

/--
[rc6_base_eq_three_pieces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6overlapsplit.lean)
-/
@[path]
private lemma rc6_base_eq_three_pieces_eq
  [DecidableEq α]
  {s K L : Finset α} :
-- imply
  s = (s ∩ K) ∪ (s ∩ L) ∪ (s \ (K ∪ L)) := by
-- proof
  apply StatMech.Walls.rc6_base_eq_three_pieces s K L

/--
[rc6_onlyK_disjoint_onlyL](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6overlapsplit.lean)
-/
@[path]
private lemma rc6_onlyK_disjoint_onlyL_eq
  [DecidableEq α]
  {K L : Finset α}
  {s : Finset α}
-- given
  (h : Disjoint K L) :
-- imply
  Disjoint (s ∩ K) (s ∩ L) := by
-- proof
  apply StatMech.Walls.rc6_onlyK_disjoint_onlyL h s

/--
[rc6_KorL_disjoint_neither](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6overlapsplit.lean)
-/
@[path]
private lemma rc6_KorL_disjoint_neither_eq
  [DecidableEq α]
  {K L : Finset α}
  {s : Finset α} :
-- imply
  Disjoint ((s ∩ K) ∪ (s ∩ L)) (s \ (K ∪ L)) := by
-- proof
  apply StatMech.Walls.rc6_KorL_disjoint_neither K L s

/--
[rc6_card_base_eq_three_pieces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6overlapsplit.lean)
-/
@[path]
private lemma rc6_card_base_eq_three_pieces_eq
  [DecidableEq α]
  {K L : Finset α}
  {s : Finset α}
-- given
  (h : Disjoint K L) :
-- imply
  #s = #(s ∩ K) + #(s ∩ L) + #(s \ (K ∪ L)) := by
-- proof
  apply StatMech.Walls.rc6_card_base_eq_three_pieces h s

/--
[rc6_witness_diagonal_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6overlapsplit.lean)
-/
@[path]
private lemma rc6_witness_diagonal_empty_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {ω : ConfigSpace α}
  {s K L : Finset α}
  {i : α}
-- given
  (hw : SupportEncodedMinimalWitness A B ω s K L) :
-- imply
  ¬ (i ∈ K ∧ i ∈ L) := by
-- proof
  apply StatMech.Walls.rc6_witness_diagonal_empty hw i

/--
[rc6_witness_overlap_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6overlapsplit.lean)
-/
@[path]
private lemma rc6_witness_overlap_trichotomy_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {ω : ConfigSpace α}
  {s K L : Finset α}
  {i : α}
-- given
  (hw : SupportEncodedMinimalWitness A B ω s K L) :
-- imply
  (i ∈ K ∧ i ∉ L) ∨ (i ∉ K ∧ i ∈ L) ∨ (i ∉ K ∧ i ∉ L) := by
-- proof
  apply StatMech.Walls.rc6_witness_overlap_trichotomy hw i

/--
[rc6_witness_card_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6overlapsplit.lean)
-/
@[path]
private lemma rc6_witness_card_split_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {ω : ConfigSpace α}
  {s K L : Finset α}
-- given
  (hw : SupportEncodedMinimalWitness A B ω s K L) :
-- imply
  #s = #(s ∩ K) + #(s ∩ L) + #(s \ (K ∪ L)) := by
-- proof
  apply StatMech.Walls.rc6_witness_card_split hw

/--
[rc6_exists_witness_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6overlapsplit.lean)
-/
@[path]
private lemma rc6_exists_witness_split_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {ω : ConfigSpace α}
-- given
  (hω : ω ∈ disjointOccurrence A B) :
-- imply
  ∃ s K L : Finset α, SupportEncodedMinimalWitness A B ω s K L ∧ ∀ i : α, ¬ (i ∈ K ∧ i ∈ L) := by
-- proof
  apply StatMech.Walls.rc6_exists_witness_split hω

/--
[rc6_overlap_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6overlapsplit.lean)
-/
@[path]
private lemma rc6_overlap_split_eq
  {K L : Set α}
  {i : α}
-- given
  (h : Disjoint K L) :
-- imply
  rc6_classify K L i ≠ both ∧ rc6_classify K L i ∈ ({neither, onlyK, onlyL} : Finset WitnessClass) ∧ ((i ∈ K ∧ i ∉ L) ∨ (i ∉ K ∧ i ∈ L) ∨ (i ∉ K ∧ i ∉ L)) := by
-- proof
  apply StatMech.Walls.rc6_overlap_split h i


-- created on 2026-10-23
