import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.Hamming
open StatMech StatMech.BeffaraDC


/--
[hammingToSet_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Hamming.lean)
-/
@[path]
private lemma hammingToSet_le_eq
  [Fintype E]
  {A : Set (ConfigSpace E)}
  {a : ConfigSpace E}
  {ω : ConfigSpace E}
-- given
  (ha : a ∈ A) :
-- imply
  hammingToSet A ω ≤ hammingDist ω a := by
-- proof
  apply StatMech.BeffaraDC.hammingToSet_le A ha ω

/--
[exists_realizer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Hamming.lean)
-/
@[path]
private lemma exists_realizer_eq
  [Fintype E]
  {A : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hne : A.Nonempty) :
-- imply
  ∃ a ∈ A, hammingDist ω a = hammingToSet A ω := by
-- proof
  apply StatMech.BeffaraDC.exists_realizer A hne ω

/--
[hammingToSet_eq_zero_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Hamming.lean)
-/
@[path]
private lemma hammingToSet_eq_zero_of_mem_eq
  [Fintype E]
  {A : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (h : ω ∈ A) :
-- imply
  hammingToSet A ω = 0 := by
-- proof
  apply StatMech.BeffaraDC.hammingToSet_eq_zero_of_mem A h

/--
[hammingToSet_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Hamming.lean)
-/
@[path]
private lemma hammingToSet_eq_zero_iff_eq
  [Fintype E]
  {A : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hne : A.Nonempty) :
-- imply
  hammingToSet A ω = 0 ↔ ω ∈ A := by
-- proof
  apply StatMech.BeffaraDC.hammingToSet_eq_zero_iff A hne ω

/--
[hammingToSet_le_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Hamming.lean)
-/
@[path]
private lemma hammingToSet_le_add_eq
  [Fintype E]
  {A : Set (ConfigSpace E)}
  {ω ω' : ConfigSpace E}
-- given
  (hne : A.Nonempty) :
-- imply
  hammingToSet A ω ≤ hammingDist ω ω' + hammingToSet A ω' := by
-- proof
  apply StatMech.BeffaraDC.hammingToSet_le_add A hne ω ω'

/--
[hammingToSet_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Hamming.lean)
-/
@[path]
private lemma hammingToSet_antitone_eq
  [Fintype E]
  {A : Set (ConfigSpace E)}
  {ω ω' : ConfigSpace E}
-- given
  (hA : IsIncreasing A)
  (hle : ω ≤ ω') :
-- imply
  hammingToSet A ω' ≤ hammingToSet A ω := by
-- proof
  apply StatMech.BeffaraDC.hammingToSet_antitone A hA hle


-- created on 2026-10-23
