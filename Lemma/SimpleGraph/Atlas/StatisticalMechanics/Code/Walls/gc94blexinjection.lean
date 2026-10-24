import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc94blexinjection
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc94b_lexPath_breaks_symmetry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc94blexinjection.lean)
-/
@[path]
private lemma gc94b_lexPath_breaks_symmetry_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  ({1} : Finset (Fin 4)) ≠ ({2} : Finset (Fin 4)) ∧ ({1} : Finset (Fin 4)).image (Equiv.swap (1 : Fin 4) 2) = ({2} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc94b_lexPath_breaks_symmetry

/--
[gc94b_lexReroute_collides_wred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc94blexinjection.lean)
-/
@[path]
private lemma gc94b_lexReroute_collides_wred_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  gc94b_dropReroute (fun K => K) (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4))) = ((∅ : Finset (Fin 4)), (∅ : Finset (Fin 4))) ∧ gc94b_dropReroute (fun K => K) (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4))) = ((∅ : Finset (Fin 4)), (∅ : Finset (Fin 4))) ∧ gc94b_dropReroute (fun K => K) (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4))) = gc94b_dropReroute (fun K => K) (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4))) := by
-- proof
  apply StatMech.Walls.gc94b_lexReroute_collides_wred

/--
[gc94b_lexStash_fails_to_land_wred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc94blexinjection.lean)
-/
@[path]
private lemma gc94b_lexStash_fails_to_land_wred_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  gc94b_stashReroute (fun K => K) (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4))) = ((∅ : Finset (Fin 4)), ({1} : Finset (Fin 4))) ∧ gc94b_stashReroute (fun K => K) (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4))) = ((∅ : Finset (Fin 4)), ({2} : Finset (Fin 4))) ∧ gc94b_stashReroute (fun K => K) (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4))) ≠ gc94b_stashReroute (fun K => K) (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4))) ∧ sources gc88b_wredEnds ({1} : Finset (Fin 4)) = ({0, 3} : Finset (Fin 4)) ∧ sources gc88b_wredEnds ({2} : Finset (Fin 4)) = ({0, 3} : Finset (Fin 4)) ∧ ({0, 3} : Finset (Fin 4)) ≠ (∅ : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc94b_lexStash_fails_to_land_wred

/--
[gc94b_lexStash_not_in_T3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc94blexinjection.lean)
-/
@[path]
private lemma gc94b_lexStash_not_in_T3_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  ((∅ : Finset (Fin 4)), ({1} : Finset (Fin 4))) ∉ gc91b_T3Pairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3 ∧ ((∅ : Finset (Fin 4)), ({2} : Finset (Fin 4))) ∉ gc91b_T3Pairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc94b_lexStash_not_in_T3

/--
[gc94b_sourceFree_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc94blexinjection.lean)
-/
@[path]
private lemma gc94b_sourceFree_classification_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {K : Finset (Fin 4)} :
-- imply
  sources gc88b_wredEnds K = (∅ : Finset (Fin 4)) ↔ (K = (∅ : Finset (Fin 4)) ∨ K = ({1, 2} : Finset (Fin 4))) := by
-- proof
  apply StatMech.Walls.gc94b_sourceFree_classification K

/--
[gc94b_sourceFree_swapFixed_wred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc94blexinjection.lean)
-/
@[path]
private lemma gc94b_sourceFree_swapFixed_wred_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {K : Finset (Fin 4)}
-- given
  (hK : sources gc88b_wredEnds K = (∅ : Finset (Fin 4))) :
-- imply
  K.image (Equiv.swap (1 : Fin 4) 2) = K := by
-- proof
  apply StatMech.Walls.gc94b_sourceFree_swapFixed_wred K hK

/--
[gc94b_all_T3_swapFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc94blexinjection.lean)
-/
@[path]
private lemma gc94b_all_T3_swapFixed_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {JJ : Finset (Fin 4) × Finset (Fin 4)}
-- given
  (hJJ : JJ ∈ gc91b_T3Pairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3) :
-- imply
  gc92b_pairAction (Equiv.swap (1 : Fin 4) 2) JJ = JJ := by
-- proof
  apply StatMech.Walls.gc94b_all_T3_swapFixed JJ hJJ

/--
[gc94b_rankMatch_is_circular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc94blexinjection.lean)
-/
@[path]
private lemma gc94b_rankMatch_is_circular_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hxg : x ≠ g) :
-- imply
  Nonempty ({KK // KK ∈ gc91b_cogxgPairs ends m o x g} ↪ {JJ // JJ ∈ gc91b_T3Pairs ends m o x y g}) ↔ gc87b_CogxgLeT3 ends m o x y g := by
-- proof
  apply StatMech.Walls.gc94b_rankMatch_is_circular ends m hnd hxg

/--
[gc94b_lex_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc94blexinjection.lean)
-/
@[path]
private lemma gc94b_lex_status_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  (({1} : Finset (Fin 4)) ≠ ({2} : Finset (Fin 4)) ∧ ({1} : Finset (Fin 4)).image (Equiv.swap (1 : Fin 4) 2) = ({2} : Finset (Fin 4))) ∧ gc94b_dropReroute (fun K => K) (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4))) = gc94b_dropReroute (fun K => K) (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4))) ∧ (gc94b_stashReroute (fun K => K) (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4))) ≠ gc94b_stashReroute (fun K => K) (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4))) ∧ ((∅ : Finset (Fin 4)), ({1} : Finset (Fin 4))) ∉ gc91b_T3Pairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3) ∧ (∀ JJ ∈ gc91b_T3Pairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3, gc92b_pairAction (Equiv.swap (1 : Fin 4) 2) JJ = JJ) := by
-- proof
  apply StatMech.Walls.gc94b_lex_status

/--
[gc94b_machine_findings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc94blexinjection.lean)
-/
@[path]
private lemma gc94b_machine_findings_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gc94b_machine_findings


-- created on 2026-10-23
