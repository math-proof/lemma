import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexEndpointPieceRigidity
open StatMech StatMech.Universality


/--
[specialMidCount_append_one_of_base_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointPieceRigidity.lean)
-/
@[path]
private lemma specialMidCount_append_one_of_base_one_eq
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {base : List ℤ}
  {t : ℤ}
  {j l : Fin 3}
-- given
  (hdu : du ≠ 0)
  (hjl : j ≠ l)
  (hbaseEnd : (ofTurns a h0 base).EndsAt (labelMid v du j))
  (hextEnd : (ofTurns a h0 (base ++ [t])).EndsAt (labelMid v du l))
  (hbaseCount : specialMidCount a h0 v du base = 1) :
-- imply
  specialMidCount a h0 v du (base ++ [t]) = 2 := by
-- proof
  apply StatMech.Universality.specialMidCount_append_one_of_base_one hdu hjl hbaseEnd hextEnd hbaseCount

/--
[HexEndpointCyclicTriplet.extension_counts_of_base_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointPieceRigidity.lean)
-/
@[path]
private lemma extension_counts_of_base_one_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {C : HexEndpointCyclicTriplet region a h0 v du}
-- given
  (hdu : du ≠ 0)
  (hbaseCount : specialMidCount a h0 v du C.base = 1) :
-- imply
  specialMidCount a h0 v du (C.base ++ [-1]) = 2 ∧ specialMidCount a h0 v du (C.base ++ [1]) = 2 := by
-- proof
  apply StatMech.Universality.HexEndpointCyclicTriplet.extension_counts_of_base_one C hdu hbaseCount

/--
[HexEndpointCyclicTriplet.count_eq_one_or_two_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointPieceRigidity.lean)
-/
@[path]
private lemma count_eq_one_or_two_of_mem_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {C : HexEndpointCyclicTriplet region a h0 v du}
  {ts : List ℤ}
-- given
  (hdu : du ≠ 0)
  (hbaseCount : specialMidCount a h0 v du C.base = 1)
  (hts : ts ∈ C.piece) :
-- imply
  specialMidCount a h0 v du ts = 1 ∨ specialMidCount a h0 v du ts = 2 := by
-- proof
  apply StatMech.Universality.HexEndpointCyclicTriplet.count_eq_one_or_two_of_mem C hdu hbaseCount hts

/--
[HexEndpointCyclicTriplet.piece_eq_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointPieceRigidity.lean)
-/
@[path]
private lemma piece_eq_of_mem_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {C D : HexEndpointCyclicTriplet region a h0 v du}
  {ts : List ℤ}
-- given
  (hdu : du ≠ 0)
  (hCbase : specialMidCount a h0 v du C.base = 1)
  (hDbase : specialMidCount a h0 v du D.base = 1)
  (hC : ts ∈ C.piece)
  (hD : ts ∈ D.piece) :
-- imply
  C.piece = D.piece := by
-- proof
  apply StatMech.Universality.HexEndpointCyclicTriplet.piece_eq_of_mem C D hdu hCbase hDbase hC hD

/--
[HexEndpointCyclicTriplet.disjoint_cyclicLoopPair_of_counts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointPieceRigidity.lean)
-/
@[path]
private lemma disjoint_cyclicLoopPair_of_counts_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {C : HexEndpointCyclicTriplet region a h0 v du}
  {P : HexEndpointCyclicLoopPair region a h0 v du}
-- given
  (hdu : du ≠ 0)
  (hCbase : specialMidCount a h0 v du C.base = 1)
  (hPsucc : specialMidCount a h0 v du (P.base ++ P.loopQ) = 3)
  (hPpred : specialMidCount a h0 v du (P.base ++ hexEndpointLoopPartner P.loopQ) = 3) :
-- imply
  Disjoint C.piece P.piece := by
-- proof
  apply StatMech.Universality.HexEndpointCyclicTriplet.disjoint_cyclicLoopPair_of_counts C P hdu hCbase hPsucc hPpred

/--
[HexEndpointCyclicLoopPair.piece_eq_of_mem_of_shared_stem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointPieceRigidity.lean)
-/
@[path]
private lemma piece_eq_of_mem_of_shared_stem_eq
  {region : ℂ → Prop}
  {v du : ℂ}
  {P Q : HexEndpointCyclicLoopPair region hexAWStart 1 v du}
  {ts : List ℤ}
-- given
  (hPstem : hexInfra_midAccum hexAWStart 1 P.base + halfStep (hexInfra_headAccum 1 P.base) = v)
  (hQstem : hexInfra_midAccum hexAWStart 1 Q.base + halfStep (hexInfra_headAccum 1 Q.base) = v)
  (hPmem : ts ∈ P.piece)
  (hQmem : ts ∈ Q.piece) :
-- imply
  P.piece = Q.piece := by
-- proof
  apply StatMech.Universality.HexEndpointCyclicLoopPair.piece_eq_of_mem_of_shared_stem P Q hPstem hQstem hPmem hQmem


-- created on 2026-10-23
