import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc2_shiftbij
open Finset BigOperators Classical StatMech StatMech.Walls


/--
[gc2_sources_shift_bijOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_shiftbij.lean)
-/
@[path]
private lemma gc2_sources_shift_bijOn_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {A : Finset V}
-- given
  (hK : K ⊆ m) :
-- imply
  Set.BijOn (fun N => N ∆ K) {N | N ⊆ m ∧ sources ends N = A} {N | N ⊆ m ∧ sources ends N = A ∆ sources ends K} := by
-- proof
  apply StatMech.Walls.gc2_sources_shift_bijOn ends m K hK A

/--
[gc2_shift_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_shiftbij.lean)
-/
@[path]
private lemma gc2_shift_involutive_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {K : Finset ι} :
-- imply
  Function.Involutive (fun N : Finset ι => N ∆ K) := by
-- proof
  apply StatMech.Walls.gc2_shift_involutive K

/--
[gc2_shift_leftInvOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_shiftbij.lean)
-/
@[path]
private lemma gc2_shift_leftInvOn_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {B : Finset V} :
-- imply
  Set.LeftInvOn (fun N => N ∆ K) (fun N => N ∆ K) {N | N ⊆ m ∧ sources ends N = B} := by
-- proof
  apply StatMech.Walls.gc2_shift_leftInvOn ends m K B

/--
[gc2_shift_bijOn_empty_to_B](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_shiftbij.lean)
-/
@[path]
private lemma gc2_shift_bijOn_empty_to_B_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {B : Finset V}
-- given
  (hK : K ⊆ m)
  (hKsrc : sources ends K = B) :
-- imply
  Set.BijOn (fun N => N ∆ K) {N | N ⊆ m ∧ sources ends N = ∅} {N | N ⊆ m ∧ sources ends N = B} := by
-- proof
  apply StatMech.Walls.gc2_shift_bijOn_empty_to_B ends m K hK B hKsrc

/--
[gc2_shift_bijOn_B_to_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_shiftbij.lean)
-/
@[path]
private lemma gc2_shift_bijOn_B_to_empty_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {B : Finset V}
-- given
  (hK : K ⊆ m)
  (hKsrc : sources ends K = B) :
-- imply
  Set.BijOn (fun N => N ∆ K) {N | N ⊆ m ∧ sources ends N = B} {N | N ⊆ m ∧ sources ends N = ∅} := by
-- proof
  apply StatMech.Walls.gc2_shift_bijOn_B_to_empty ends m K hK B hKsrc

/--
[gc2_shift_involution_empty_B](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_shiftbij.lean)
-/
@[path]
private lemma gc2_shift_involution_empty_B_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {B : Finset V}
-- given
  (hK : K ⊆ m)
  (hKsrc : sources ends K = B) :
-- imply
  Set.BijOn (fun N => N ∆ K) {N | N ⊆ m ∧ sources ends N = B} {N | N ⊆ m ∧ sources ends N = ∅} ∧ Set.LeftInvOn (fun N => N ∆ K) (fun N => N ∆ K) {N | N ⊆ m ∧ sources ends N = B} ∧ Set.RightInvOn (fun N => N ∆ K) (fun N => N ∆ K) {N | N ⊆ m ∧ sources ends N = ∅} := by
-- proof
  apply StatMech.Walls.gc2_shift_involution_empty_B ends m K hK B hKsrc


-- created on 2026-10-23
