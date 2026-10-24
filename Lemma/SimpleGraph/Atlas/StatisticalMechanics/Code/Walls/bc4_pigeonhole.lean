import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc4_pigeonhole
open Set StatMech StatMech.Walls


/--
[bc4_finite_biUnion_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_pigeonhole.lean)
-/
@[path]
private lemma bc4_finite_biUnion_infinite_eq
  {S : Set ι}
  {f : ι → Set α}
-- given
  (hS : S.Finite)
  (hinf : (⋃ i ∈ S, f i).Infinite) :
-- imply
  ∃ i ∈ S, (f i).Infinite := by
-- proof
  apply StatMech.Walls.bc4_finite_biUnion_infinite hS hinf

/--
[bc4_finite_iUnion_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_pigeonhole.lean)
-/
@[path]
private lemma bc4_finite_iUnion_infinite_eq
  [Empty.Finite ι]
  {f : ι → Set α}
-- given
  (hinf : (⋃ i, f i).Infinite) :
-- imply
  ∃ i, (f i).Infinite := by
-- proof
  apply StatMech.Walls.bc4_finite_iUnion_infinite hinf

/--
[bc4_finset_biUnion_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_pigeonhole.lean)
-/
@[path]
private lemma bc4_finset_biUnion_infinite_eq
  {s : Finset ι}
  {f : ι → Set α}
-- given
  (hinf : (⋃ i ∈ s, f i).Infinite) :
-- imply
  ∃ i ∈ s, (f i).Infinite := by
-- proof
  apply StatMech.Walls.bc4_finset_biUnion_infinite s hinf

/--
[bc4_finite_sUnion_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_pigeonhole.lean)
-/
@[path]
private lemma bc4_finite_sUnion_infinite_eq
  {C : Set (Set α)}
-- given
  (hC : C.Finite)
  (hinf : (⋃₀ C).Infinite) :
-- imply
  ∃ t ∈ C, Set.Infinite t := by
-- proof
  apply StatMech.Walls.bc4_finite_sUnion_infinite hC hinf


-- created on 2026-10-23
