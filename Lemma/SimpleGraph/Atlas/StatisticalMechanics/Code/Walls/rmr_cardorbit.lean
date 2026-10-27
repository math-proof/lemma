import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rmr_cardorbit.Part2
open Finset StatMech StatMech.Walls


/--
[slabBox_def](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cardorbit.lean)
-/
@[path]
private lemma slabBox_def_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  slabBox A B k = poc_slabBox A B k := by
-- proof
  apply StatMech.Walls.slabBox_def A B k

/--
[slabImg_def](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cardorbit.lean)
-/
@[path]
private lemma slabImg_def_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  slabImg A B k = poc_slabImg A B k := by
-- proof
  apply StatMech.Walls.slabImg_def A B k

/--
[mem_slabBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cardorbit.lean)
-/
@[path]
private lemma mem_slabBox_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α} :
-- imply
  ω ∈ slabBox A B k ↔ ω ∈ disjointOccurrence A B ∧ orbitKey (ω, poc_keyFlip k ω) = k := by
-- proof
  apply StatMech.Walls.mem_slabBox

/--
[mem_slabImg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cardorbit.lean)
-/
@[path]
private lemma mem_slabImg_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α} :
-- imply
  ω ∈ slabImg A B k ↔ ω ∈ A ∧ poc_keyFlip k ω ∈ B ∧ orbitKey (ω, poc_keyFlip k ω) = k := by
-- proof
  apply StatMech.Walls.mem_slabImg

/--
[mem_boxOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cardorbit.lean)
-/
@[path]
private lemma mem_boxOrbit_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {k : ConfigSpace α × ConfigSpace α}
  {p : ConfigSpace α × ConfigSpace α} :
-- imply
  p ∈ boxOrbit A B k ↔ p.1 ∈ disjointOccurrence A B ∧ orbitKey p = k := by
-- proof
  apply StatMech.Walls.mem_boxOrbit

/--
[mem_imgOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cardorbit.lean)
-/
@[path]
private lemma mem_imgOrbit_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {k : ConfigSpace α × ConfigSpace α}
  {q : ConfigSpace α × ConfigSpace α} :
-- imply
  q ∈ imgOrbit A B k ↔ q.1 ∈ A ∧ q.2 ∈ B ∧ orbitKey q = k := by
-- proof
  apply StatMech.Walls.mem_imgOrbit

/--
[pair_eq_of_orbitKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cardorbit.lean)
-/
@[path]
private lemma pair_eq_of_orbitKey_eq
  [Fintype α]
  [DecidableEq α]
  {p : ConfigSpace α × ConfigSpace α}
  {k : ConfigSpace α × ConfigSpace α}
-- given
  (hk : orbitKey p = k) :
-- imply
  p = (p.1, poc_keyFlip k p.1) := by
-- proof
  apply StatMech.Walls.pair_eq_of_orbitKey hk

/--
[cardOrbit_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cardorbit.lean)
-/
@[path]
private lemma cardOrbit_box_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  #(boxOrbit A B k) = #(slabBox A B k) := by
-- proof
  apply StatMech.Walls.cardOrbit_box A B k

/--
[cardOrbit_img](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cardorbit.lean)
-/
@[path]
private lemma cardOrbit_img_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  #(imgOrbit A B k) = #(slabImg A B k) := by
-- proof
  apply StatMech.Walls.cardOrbit_img A B k

/--
[cardOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cardorbit.lean)
-/
@[path]
private lemma cardOrbit_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  #(boxOrbit A B k) = #(slabBox A B k) ∧ #(imgOrbit A B k) = #(slabImg A B k) := by
-- proof
  apply StatMech.Walls.cardOrbit A B k


-- created on 2026-10-23
