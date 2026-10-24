import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc3_slabcardiffperkey
open Finset StatMech StatMech.Walls


/--
[rc3_slabBox_eq_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabcardiffperkey.lean)
-/
@[path]
private lemma rc3_slabBox_eq_inter_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  poc_slabBox A B k = Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k) := by
-- proof
  apply StatMech.Walls.rc3_slabBox_eq_inter A B k

/--
[rc3_slabCardKey_iff_perKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabcardiffperkey.lean)
-/
@[path]
private lemma rc3_slabCardKey_iff_perKey_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  (#(poc_slabBox A B k) ≤ #(poc_slabImg A B k)) ↔ rc3_PerKey A B k := by
-- proof
  apply StatMech.Walls.rc3_slabCardKey_iff_perKey A B k

/--
[rc3_slabCard_iff_perKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabcardiffperkey.lean)
-/
@[path]
private lemma rc3_slabCard_iff_perKey_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  poc_SlabCard A B ↔ ∀ k : ConfigSpace α × ConfigSpace α, rc3_PerKey A B k := by
-- proof
  apply StatMech.Walls.rc3_slabCard_iff_perKey A B

/--
[rc3_perKey_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabcardiffperkey.lean)
-/
@[path]
private lemma rc3_perKey_top_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  rc3_PerKey A B poc_topKey ↔ #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) ≤ #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
-- proof
  apply StatMech.Walls.rc3_perKey_top A B

/--
[rc3_perKeyAll_iff_slabCardAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabcardiffperkey.lean)
-/
@[path]
private lemma rc3_perKeyAll_iff_slabCardAll_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc3_PerKeyAll ↔ StatMech.poc_SlabCardAll := by
-- proof
  apply StatMech.Walls.rc3_perKeyAll_iff_slabCardAll

/--
[rc3_reimerWprobCore_of_perKeyAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabcardiffperkey.lean)
-/
@[path]
private lemma rc3_reimerWprobCore_of_perKeyAll_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc3_PerKeyAll) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc3_reimerWprobCore_of_perKeyAll h

/--
[rc3_reimer_inequality_of_perKeyAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabcardiffperkey.lean)
-/
@[path]
private lemma rc3_reimer_inequality_of_perKeyAll_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (h : rc3_PerKeyAll)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.Walls.rc3_reimer_inequality_of_perKeyAll h hp A B

/--
[rc3_perKey_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabcardiffperkey.lean)
-/
@[path]
private lemma rc3_perKey_rbi_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)} :
-- imply
  rc3_PerKey rbi_A rbi_B k := by
-- proof
  apply StatMech.Walls.rc3_perKey_rbi k

/--
[rc3_perKey_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabcardiffperkey.lean)
-/
@[path]
private lemma rc3_perKey_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
  {k : ConfigSpace α × ConfigSpace α}
-- given
  (hA : DependsOn A (↑S))
  (hB : DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  rc3_PerKey A B k := by
-- proof
  apply StatMech.Walls.rc3_perKey_of_disjoint_support hA hB hST k

/--
[rc3_perKey_of_box_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabcardiffperkey.lean)
-/
@[path]
private lemma rc3_perKey_of_box_empty_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {k : ConfigSpace α × ConfigSpace α}
-- given
  (hbox : disjointOccurrence A B = ∅) :
-- imply
  rc3_PerKey A B k := by
-- proof
  apply StatMech.Walls.rc3_perKey_of_box_empty hbox k


-- created on 2026-10-23
