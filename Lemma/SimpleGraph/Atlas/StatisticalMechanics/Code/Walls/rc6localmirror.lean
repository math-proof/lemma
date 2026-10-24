import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc6localmirror
open Finset StatMech StatMech.Walls


/--
[rc6_localMirror_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_localMirror_apply_eq
  [Fintype α]
  [DecidableEq α]
  {L : Set α}
  {i : α}
  {ω : ConfigSpace α}
  {a : α} :
-- imply
  rc6_localMirror L i ω a = if a = i ∧ i ∈ L then !ω a else ω a := by
-- proof
  apply StatMech.Walls.rc6_localMirror_apply L i ω a

/--
[rc6_localMirror_at_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_localMirror_at_mem_eq
  [Fintype α]
  [DecidableEq α]
  {L : Set α}
  {i : α}
  {ω : ConfigSpace α}
-- given
  (hi : i ∈ L) :
-- imply
  rc6_localMirror L i ω i = !ω i := by
-- proof
  apply StatMech.Walls.rc6_localMirror_at_mem L i ω hi

/--
[rc6_localMirror_at_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_localMirror_at_not_mem_eq
  [Fintype α]
  [DecidableEq α]
  {L : Set α}
  {i : α}
  {ω : ConfigSpace α}
-- given
  (hi : i ∉ L) :
-- imply
  rc6_localMirror L i ω i = ω i := by
-- proof
  apply StatMech.Walls.rc6_localMirror_at_not_mem L i ω hi

/--
[rc6_localMirror_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_localMirror_off_eq
  [Fintype α]
  [DecidableEq α]
  {L : Set α}
  {i : α}
  {ω : ConfigSpace α}
  {a : α}
-- given
  (ha : a ≠ i) :
-- imply
  rc6_localMirror L i ω a = ω a := by
-- proof
  apply StatMech.Walls.rc6_localMirror_off L i ω ha

/--
[rc6_localMirror_localMirror](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_localMirror_localMirror_eq
  [Fintype α]
  [DecidableEq α]
  {L : Set α}
  {i : α}
  {ω : ConfigSpace α} :
-- imply
  rc6_localMirror L i (rc6_localMirror L i ω) = ω := by
-- proof
  apply StatMech.Walls.rc6_localMirror_localMirror L i ω

/--
[rc6_localMirror_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_localMirror_involutive_eq
  [Fintype α]
  [DecidableEq α]
  {L : Set α}
  {i : α} :
-- imply
  Function.Involutive (rc6_localMirror L i) := by
-- proof
  apply StatMech.Walls.rc6_localMirror_involutive L i

/--
[rc6_localMirror_involutive_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_localMirror_involutive_at_eq
  [Fintype α]
  [DecidableEq α]
  {L : Set α}
  {i : α}
  {ω : ConfigSpace α} :
-- imply
  rc6_localMirror L i (rc6_localMirror L i ω) i = ω i := by
-- proof
  apply StatMech.Walls.rc6_localMirror_involutive_at L i ω

/--
[rc6_localMirror_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_localMirror_injective_eq
  [Fintype α]
  [DecidableEq α]
  {L : Set α}
  {i : α} :
-- imply
  Function.Injective (rc6_localMirror L i) := by
-- proof
  apply StatMech.Walls.rc6_localMirror_injective L i

/--
[rc6_localMirror_agreeOn_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_localMirror_agreeOn_of_disjoint_eq
  [Fintype α]
  [DecidableEq α]
  {K L : Set α}
  {i : α}
  {ω : ConfigSpace α}
-- given
  (hKL : Disjoint K L) :
-- imply
  agreeOn K ω (rc6_localMirror L i ω) := by
-- proof
  apply StatMech.Walls.rc6_localMirror_agreeOn_of_disjoint i ω hKL

/--
[rc6_localMirror_mem_A](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_localMirror_mem_A_eq
  [Fintype α]
  [DecidableEq α]
  {A : Set (ConfigSpace α)}
  {K L : Set α}
  {i : α}
  {ω : ConfigSpace α}
-- given
  (hKL : Disjoint K L)
  (hA : OccursOn A K ω) :
-- imply
  rc6_localMirror L i ω ∈ A := by
-- proof
  apply StatMech.Walls.rc6_localMirror_mem_A i hKL hA

/--
[rc6_localMirror_eq_compl_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_localMirror_eq_compl_at_eq
  [Fintype α]
  [DecidableEq α]
  {L : Set α}
  {i : α}
  {ω : ConfigSpace α}
-- given
  (hi : i ∈ L) :
-- imply
  rc6_localMirror L i ω i = rmr_compl ω i := by
-- proof
  apply StatMech.Walls.rc6_localMirror_eq_compl_at i ω hi

/--
[rc6_localMirror_node](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_localMirror_node_eq
  [Fintype α]
  [DecidableEq α]
  {A : Set (ConfigSpace α)}
  {K L : Set α}
  {i : α}
  {ω : ConfigSpace α}
-- given
  (hKL : Disjoint K L)
  (hA : OccursOn A K ω) :
-- imply
  (∀ a, a ≠ i → rc6_localMirror L i ω a = ω a) ∧ (i ∈ L → rc6_localMirror L i ω i = !ω i) ∧ (i ∉ L → rc6_localMirror L i ω i = ω i) ∧ rc6_localMirror L i (rc6_localMirror L i ω) i = ω i ∧ rc6_localMirror L i ω ∈ A ∧ (i ∈ L → rc6_localMirror L i ω i = rmr_compl ω i) := by
-- proof
  apply StatMech.Walls.rc6_localMirror_node i hKL hA

/--
[rc6_mirrorL_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_mirrorL_apply_eq
  [Fintype α]
  [DecidableEq α]
  {L : Set α}
  {ω : ConfigSpace α}
  {a : α} :
-- imply
  rc6_mirrorL L ω a = if a ∈ L then !ω a else ω a := by
-- proof
  apply StatMech.Walls.rc6_mirrorL_apply L ω a

/--
[rc6_mirrorL_eq_localMirror_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_mirrorL_eq_localMirror_diag_eq
  [Fintype α]
  [DecidableEq α]
  {L : Set α}
  {ω : ConfigSpace α}
  {a : α} :
-- imply
  rc6_mirrorL L ω a = rc6_localMirror L a ω a := by
-- proof
  apply StatMech.Walls.rc6_mirrorL_eq_localMirror_diag L ω a

/--
[rc6_mirrorL_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_mirrorL_involutive_eq
  [Fintype α]
  [DecidableEq α]
  {L : Set α} :
-- imply
  Function.Involutive (rc6_mirrorL L) := by
-- proof
  apply StatMech.Walls.rc6_mirrorL_involutive L

/--
[rc6_mirrorL_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_mirrorL_injective_eq
  [Fintype α]
  [DecidableEq α]
  {L : Set α} :
-- imply
  Function.Injective (rc6_mirrorL L) := by
-- proof
  apply StatMech.Walls.rc6_mirrorL_injective L

/--
[rc6_mirrorL_agreeOn_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_mirrorL_agreeOn_of_disjoint_eq
  [Fintype α]
  [DecidableEq α]
  {K L : Set α}
  {ω : ConfigSpace α}
-- given
  (hKL : Disjoint K L) :
-- imply
  agreeOn K ω (rc6_mirrorL L ω) := by
-- proof
  apply StatMech.Walls.rc6_mirrorL_agreeOn_of_disjoint ω hKL

/--
[rc6_compl_mirrorL_agreeOn_L](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_compl_mirrorL_agreeOn_L_eq
  [Fintype α]
  [DecidableEq α]
  {L : Set α}
  {ω : ConfigSpace α} :
-- imply
  agreeOn L ω (rmr_compl (rc6_mirrorL L ω)) := by
-- proof
  apply StatMech.Walls.rc6_compl_mirrorL_agreeOn_L L ω

/--
[rc6_mirrorL_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_mirrorL_mem_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {K L : Set α}
  {ω : ConfigSpace α}
-- given
  (hKL : Disjoint K L)
  (hA : OccursOn A K ω)
  (hB : OccursOn B L ω) :
-- imply
  rc6_mirrorL L ω ∈ A ∩ rmr_reflect B := by
-- proof
  apply StatMech.Walls.rc6_mirrorL_mem hKL hA hB

/--
[rc6_boxReflectInjection_of_uniformWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_boxReflectInjection_of_uniformWitness_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {K L : Set α}
-- given
  (hKL : Disjoint K L)
  (hA : ∀ ω, ω ∈ disjointOccurrence A B → OccursOn A K ω)
  (hB : ∀ ω, ω ∈ disjointOccurrence A B → OccursOn B L ω) :
-- imply
  rc5_BoxReflectInjection A B := by
-- proof
  apply StatMech.Walls.rc6_boxReflectInjection_of_uniformWitness hKL hA hB

/--
[rc6_boxReflectInjection_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean)
-/
@[path]
private lemma rc6_boxReflectInjection_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : DependsOn A (↑S))
  (hB : DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  rc5_BoxReflectInjection A B := by
-- proof
  apply StatMech.Walls.rc6_boxReflectInjection_of_disjoint_support hA hB hST


-- created on 2026-10-23
