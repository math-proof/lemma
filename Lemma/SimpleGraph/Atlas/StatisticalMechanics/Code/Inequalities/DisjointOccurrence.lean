import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
open StatMech


/--
[agreeOn_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/DisjointOccurrence.lean)
-/
@[path]
private lemma agreeOn_refl_eq
  {K : Set E}
  {ω : ConfigSpace E} :
-- imply
  agreeOn K ω ω := by
-- proof
  apply StatMech.agreeOn_refl K ω

/--
[agreeOn_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/DisjointOccurrence.lean)
-/
@[path]
private lemma agreeOn_symm_eq
  {K : Set E}
  {ω ω' : ConfigSpace E}
-- given
  (h : agreeOn K ω ω') :
-- imply
  agreeOn K ω' ω := by
-- proof
  apply StatMech.agreeOn_symm h

/--
[agreeOn_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/DisjointOccurrence.lean)
-/
@[path]
private lemma agreeOn_trans_eq
  {K : Set E}
  {ω ω' ω'' : ConfigSpace E}
-- given
  (h : agreeOn K ω ω')
  (h' : agreeOn K ω' ω'') :
-- imply
  agreeOn K ω ω'' := by
-- proof
  apply StatMech.agreeOn_trans h h'

/--
[agreeOn_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/DisjointOccurrence.lean)
-/
@[path]
private lemma agreeOn_mono_eq
  {K K' : Set E}
  {ω ω' : ConfigSpace E}
-- given
  (hKK' : K ⊆ K')
  (h : agreeOn K' ω ω') :
-- imply
  agreeOn K ω ω' := by
-- proof
  apply StatMech.agreeOn_mono hKK' h

/--
[OccursOn.mem_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/DisjointOccurrence.lean)
-/
@[path]
private lemma mem_self_eq
  {A : Set (ConfigSpace E)}
  {K : Set E}
  {ω : ConfigSpace E}
-- given
  (h : OccursOn A K ω) :
-- imply
  ω ∈ A := by
-- proof
  apply StatMech.OccursOn.mem_self h

/--
[OccursOn.mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/DisjointOccurrence.lean)
-/
@[path]
private lemma mono_eq
  {A : Set (ConfigSpace E)}
  {K K' : Set E}
  {ω : ConfigSpace E}
-- given
  (h : OccursOn A K ω)
  (hKK' : K ⊆ K') :
-- imply
  OccursOn A K' ω := by
-- proof
  apply StatMech.OccursOn.mono h hKK'

/--
[OccursOn.mono_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/DisjointOccurrence.lean)
-/
@[path]
private lemma mono_event_eq
  {A B : Set (ConfigSpace E)}
  {K : Set E}
  {ω : ConfigSpace E}
-- given
  (h : OccursOn A K ω)
  (hAB : A ⊆ B) :
-- imply
  OccursOn B K ω := by
-- proof
  apply StatMech.OccursOn.mono_event h hAB

/--
[mem_disjointOccurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/DisjointOccurrence.lean)
-/
@[path]
private lemma mem_disjointOccurrence_eq
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  ω ∈ disjointOccurrence A B ↔ ∃ K L : Set E, Disjoint K L ∧ OccursOn A K ω ∧ OccursOn B L ω := by
-- proof
  apply StatMech.mem_disjointOccurrence

/--
[disjointOccurrence_notation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/DisjointOccurrence.lean)
-/
@[path]
private lemma disjointOccurrence_notation_eq
  {A B : Set (ConfigSpace E)} :
-- imply
  (A □ B : Set (ConfigSpace E)) = disjointOccurrence A B := by
-- proof
  apply StatMech.disjointOccurrence_notation A B

/--
[disjointOccurrence_subset_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/DisjointOccurrence.lean)
-/
@[path]
private lemma disjointOccurrence_subset_inter_eq
  {A B : Set (ConfigSpace E)} :
-- imply
  disjointOccurrence A B ⊆ A ∩ B := by
-- proof
  apply StatMech.disjointOccurrence_subset_inter A B

/--
[disjointOccurrence_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/DisjointOccurrence.lean)
-/
@[path]
private lemma disjointOccurrence_comm_eq
  {A B : Set (ConfigSpace E)} :
-- imply
  disjointOccurrence A B = disjointOccurrence B A := by
-- proof
  apply StatMech.disjointOccurrence_comm A B

/--
[disjointOccurrence_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/DisjointOccurrence.lean)
-/
@[path]
private lemma disjointOccurrence_mono_eq
  {A A' B B' : Set (ConfigSpace E)}
-- given
  (hA : A ⊆ A')
  (hB : B ⊆ B') :
-- imply
  disjointOccurrence A B ⊆ disjointOccurrence A' B' := by
-- proof
  apply StatMech.disjointOccurrence_mono hA hB


-- created on 2026-10-23
