import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointCyclicAtomSupport
open StatMech StatMech.Universality


/--
[endpointCombinedSummand_ne_zero_of_valid_at_label](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCyclicAtomSupport.lean)
-/
@[path]
private lemma endpointCombinedSummand_ne_zero_of_valid_at_label_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {j : Fin 3}
  {ts : List ℤ}
-- given
  (hdu : du ≠ 0)
  (hvalid : (ofTurns a h0 ts).EndpointIsLegalSAW ∧ (ofTurns a h0 ts).StaysIn region ∧ (ofTurns a h0 ts).EndsAt (labelMid v du j)) :
-- imply
  endpointCombinedSummand region a h0 v du ts ≠ 0 := by
-- proof
  apply StatMech.Universality.endpointCombinedSummand_ne_zero_of_valid_at_label hdu j hvalid

/--
[HexEndpointCyclicTriplet.piece_subset_endpointCombinedSupportFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCyclicAtomSupport.lean)
-/
@[path]
private lemma piece_subset_endpointCombinedSupportFinset_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {C : HexEndpointCyclicTriplet R.inRegion a h0 v du}
-- given
  (hdu : du ≠ 0) :
-- imply
  C.piece ⊆ R.endpointCombinedSupportFinset a h0 v du := by
-- proof
  apply StatMech.Universality.HexEndpointCyclicTriplet.piece_subset_endpointCombinedSupportFinset hdu C

/--
[HexEndpointCyclicLoopPair.piece_subset_endpointCombinedSupportFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCyclicAtomSupport.lean)
-/
@[path]
private lemma piece_subset_endpointCombinedSupportFinset_eq_2
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {P : HexEndpointCyclicLoopPair R.inRegion a h0 v du}
-- given
  (hdu : du ≠ 0) :
-- imply
  P.piece ⊆ R.endpointCombinedSupportFinset a h0 v du := by
-- proof
  apply StatMech.Universality.HexEndpointCyclicLoopPair.piece_subset_endpointCombinedSupportFinset hdu P

/--
[HexEndpointCyclicLocalAtom.piece_subset_endpointCombinedSupportFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCyclicAtomSupport.lean)
-/
@[path]
private lemma piece_subset_endpointCombinedSupportFinset_eq_3
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {A : HexEndpointCyclicLocalAtom R.inRegion a h0 v du}
-- given
  (hdu : du ≠ 0) :
-- imply
  A.piece ⊆ R.endpointCombinedSupportFinset a h0 v du := by
-- proof
  apply StatMech.Universality.HexEndpointCyclicLocalAtom.piece_subset_endpointCombinedSupportFinset hdu A

/--
[HexEndpointCyclicLocalAtom.mem_endpointCombinedSupportFinset_of_mem_piece](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCyclicAtomSupport.lean)
-/
@[path]
private lemma mem_endpointCombinedSupportFinset_of_mem_piece_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {A : HexEndpointCyclicLocalAtom R.inRegion a h0 v du}
  {ts : List ℤ}
-- given
  (hdu : du ≠ 0)
  (hts : ts ∈ A.piece) :
-- imply
  ts ∈ R.endpointCombinedSupportFinset a h0 v du := by
-- proof
  apply StatMech.Universality.HexEndpointCyclicLocalAtom.mem_endpointCombinedSupportFinset_of_mem_piece hdu A hts


-- created on 2026-10-23
