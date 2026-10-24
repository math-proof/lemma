import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexEndpointLocalPartitionClosure
open StatMech StatMech.Universality


/--
[finitePiecePartition_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalPartitionClosure.lean)
-/
@[path]
private lemma finitePiecePartition_exists_eq
  [DecidableEq α]
  [DecidableEq ι]
  {support : Finset α}
  {piece : ι → Finset α}
-- given
  (hcover : ∀ x ∈ support, ∃ i : ι, x ∈ piece i ∧ piece i ⊆ support)
  (hoverlap : ∀ i j : ι, ∀ x ∈ support, x ∈ piece i → x ∈ piece j → piece i = piece j) :
-- imply
  ∃ atoms : Finset ι, atoms.biUnion piece = support ∧ (↑atoms : Set ι).PairwiseDisjoint piece := by
-- proof
  apply StatMech.Universality.finitePiecePartition_exists support piece hcover hoverlap


-- created on 2026-10-23
