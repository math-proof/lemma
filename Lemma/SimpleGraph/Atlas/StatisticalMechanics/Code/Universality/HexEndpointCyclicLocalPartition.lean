import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointCyclicLocalPartition.Part2
open StatMech StatMech.Universality


/--
[HexEndpointCyclicLocalAtom.sum_piece_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCyclicLocalPartition.lean)
-/
@[path]
private lemma sum_piece_zero_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {A : HexEndpointCyclicLocalAtom region a h0 v du}
-- given
  (hdu : du ≠ 0) :
-- imply
  ∑ ts ∈ A.piece, endpointCombinedSummand region a h0 v du ts = 0 := by
-- proof
  apply StatMech.Universality.HexEndpointCyclicLocalAtom.sum_piece_zero hdu A

/--
[HexEndpointCyclicLocalPartition.vertex_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCyclicLocalPartition.lean)
-/
@[path]
private lemma vertex_relation_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {P : HexEndpointCyclicLocalPartition R a h0 v du}
-- given
  (hdu : du ≠ 0) :
-- imply
  ((v + du) - v) * endpointParafObservable R.inRegion a h0 (v + du) (5 / 8) hexChi + ((v + hexOmega * du) - v) * endpointParafObservable R.inRegion a h0 (v + hexOmega * du) (5 / 8) hexChi + ((v + hexOmega ^ 2 * du) - v) * endpointParafObservable R.inRegion a h0 (v + hexOmega ^ 2 * du) (5 / 8) hexChi = 0 := by
-- proof
  apply StatMech.Universality.HexEndpointCyclicLocalPartition.vertex_relation hdu P


-- created on 2026-10-23
