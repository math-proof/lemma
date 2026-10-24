import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion
open Finset Matrix StatMech StatMech.FrontierD


/--
[mem_sixVertexBetheCyclicIntervalTuples](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma mem_sixVertexBetheCyclicIntervalTuples_eq
  {n : Nat}
  {N : Nat}
-- given
  (x q : Fin (n + 1) -> Int) :
-- imply
  q ∈ sixVertexBetheCyclicIntervalTuples N x ↔ forall i, sixVertexBetheShiftCoordinates N x i <= q i /\ q i <= x i := by
-- proof
  apply StatMech.FrontierD.mem_sixVertexBetheCyclicIntervalTuples N x q

/--
[mem_sixVertexBetheCollisionSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma mem_sixVertexBetheCollisionSet_eq
  {n : Nat}
  {N : Nat}
  {i : Fin (n + 1)}
-- given
  (x q : Fin (n + 1) -> Int) :
-- imply
  i ∈ sixVertexBetheCollisionSet N x q ↔ sixVertexBetheCollision N x q i := by
-- proof
  apply StatMech.FrontierD.mem_sixVertexBetheCollisionSet N x q i

/--
[sixVertexBetheCollisionFreeIntervalSum_inclusionExclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma sixVertexBetheCollisionFreeIntervalSum_inclusionExclusion_eq
  {n : Nat}
  {N : Nat}
  {c : Real}
-- given
  (z : Fin (n + 1) -> Complex)
  (x : Fin (n + 1) -> Int) :
-- imply
  sixVertexBetheCollisionFreeIntervalSum N c z x = ∑ S ∈ (Finset.univ : Finset (Fin (n + 1))).powerset, (-1 : Complex) ^ S.card * sixVertexBetheCollisionConstrainedIntervalSum N c z x S := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheCollisionFreeIntervalSum_inclusionExclusion N c z x

/--
[sixVertexBethe_geometricInterval_int](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma sixVertexBethe_geometricInterval_int_eq
  {c : Real}
  {z : Complex}
  {a b : Int}
-- given
  (hz0 : z ≠ 0)
  (hz1 : z ≠ 1)
  (hab : a < b) :
-- imply
  z ^ a + (c : Complex) ^ 2 * (∑ y ∈ Finset.Ioo a b, z ^ y) + z ^ b = sixVertexBetheL c z * z ^ a + sixVertexBetheM c z * z ^ b := by
-- proof
  apply StatMech.FrontierD.sixVertexBethe_geometricInterval_int c hz0 hz1 hab

/--
[sixVertexBethe_intervalLocalSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma sixVertexBethe_intervalLocalSum_eq
  {c : Real}
  {z : Complex}
  {a b : Int}
-- given
  (hz0 : z ≠ 0)
  (hz1 : z ≠ 1)
  (hab : a < b) :
-- imply
  (∑ y ∈ Finset.Icc a b, (if y = a \/ y = b then 1 else (c : Complex) ^ 2) * z ^ y) = sixVertexBetheL c z * z ^ a + sixVertexBetheM c z * z ^ b := by
-- proof
  apply StatMech.FrontierD.sixVertexBethe_intervalLocalSum c hz0 hz1 hab

/--
[sixVertexBetheCollisionConstrainedIntervalSum_eq_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma sixVertexBetheCollisionConstrainedIntervalSum_eq_prod_eq
  {n : Nat}
  {N : Nat}
  {c : Real}
  {S : Finset (Fin (n + 1))}
-- given
  (z : Fin (n + 1) -> Complex)
  (x : Fin (n + 1) -> Int)
  (hS : SixVertexBetheNoAdjacent S)
  (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i ≤ x i) :
-- imply
  sixVertexBetheCollisionConstrainedIntervalSum N c z x S = ∏ i, ∑ y ∈ sixVertexBetheConstrainedCoordinateSet N x S i, (if y = sixVertexBetheShiftCoordinates N x i \/ y = x i then 1 else (c : Complex) ^ 2) * z i ^ y := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheCollisionConstrainedIntervalSum_eq_prod N c z x S hS hgap

/--
[sixVertexBetheCollisionConstrainedIntervalSum_eq_LMprod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma sixVertexBetheCollisionConstrainedIntervalSum_eq_LMprod_eq
  {n : Nat}
  {N : Nat}
  {c : Real}
  {S : Finset (Fin (n + 1))}
-- given
  (z : Fin (n + 1) -> Complex)
  (x : Fin (n + 1) -> Int)
  (hS : SixVertexBetheNoAdjacent S)
  (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i)
  (hz0 : ∀ i, z i ≠ 0)
  (hz1 : ∀ i, z i ≠ 1) :
-- imply
  sixVertexBetheCollisionConstrainedIntervalSum N c z x S = ∏ i, if i ∈ S then z i ^ x i else if (finRotate (n + 1)).symm i ∈ S then z i ^ (sixVertexBetheShiftCoordinates N x i) else sixVertexBetheL c (z i) * z i ^ (sixVertexBetheShiftCoordinates N x i) + sixVertexBetheM c (z i) * z i ^ x i := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheCollisionConstrainedIntervalSum_eq_LMprod N c z x S hS hgap hz0 hz1

/--
[sixVertexBetheCollisionFreeIntervalSum_eq_rawWords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma sixVertexBetheCollisionFreeIntervalSum_eq_rawWords_eq
  {n : Nat}
  {N : Nat}
  {c : Real}
-- given
  (z : Fin (n + 1) -> Complex)
  (x : Fin (n + 1) -> Int)
  (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i)
  (hz0 : ∀ i, z i ≠ 0)
  (hz1 : ∀ i, z i ≠ 1) :
-- imply
  sixVertexBetheCollisionFreeIntervalSum N c z x = ∑ w ∈ (Finset.univ : Finset (Fin (n + 1))).powerset, sixVertexBetheRawIEWordCoefficient c z w * ((∏ i ∈ w, z i ^ (sixVertexBetheShiftCoordinates N x i)) * ∏ i ∈ (Finset.univ \ w), z i ^ x i) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheCollisionFreeIntervalSum_eq_rawWords N c z x hgap hz0 hz1

/--
[mem_sixVertexBetheWordMLSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma mem_sixVertexBetheWordMLSet_eq
  {n : Nat}
  {w : Finset (Fin (n + 1))}
  {i : Fin (n + 1)} :
-- imply
  i ∈ sixVertexBetheWordMLSet w ↔ i ∉ w ∧ finRotate (n + 1) i ∈ w := by
-- proof
  apply StatMech.FrontierD.mem_sixVertexBetheWordMLSet w i

/--
[sixVertexBetheWordMLSet_noAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma sixVertexBetheWordMLSet_noAdjacent_eq
  {n : Nat}
  {w : Finset (Fin (n + 1))} :
-- imply
  SixVertexBetheNoAdjacent (sixVertexBetheWordMLSet w) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheWordMLSet_noAdjacent w

/--
[sixVertexBetheRawIEWordCoefficient_eq_wordCoefficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma sixVertexBetheRawIEWordCoefficient_eq_wordCoefficient_eq
  {n : Nat}
  {c : Real}
  {w : Finset (Fin (n + 1))}
-- given
  (z : Fin (n + 1) -> Complex) :
-- imply
  sixVertexBetheRawIEWordCoefficient c z w = sixVertexBetheWordCoefficient c z (Equiv.refl _) w := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheRawIEWordCoefficient_eq_wordCoefficient c z w

/--
[sixVertexBetheCollisionFreeIntervalSum_eq_words](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma sixVertexBetheCollisionFreeIntervalSum_eq_words_eq
  {n : Nat}
  {N : Nat}
  {c : Real}
-- given
  (z : Fin (n + 1) -> Complex)
  (x : Fin (n + 1) -> Int)
  (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i)
  (hz0 : ∀ i, z i ≠ 0)
  (hz1 : ∀ i, z i ≠ 1) :
-- imply
  sixVertexBetheCollisionFreeIntervalSum N c z x = ∑ w : Finset (Fin (n + 1)), sixVertexBetheWordCoefficient c z (Equiv.refl _) w * sixVertexBetheWordMonomial N z (Equiv.refl _) x w := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheCollisionFreeIntervalSum_eq_words N c z x hgap hz0 hz1

/--
[sixVertexBetheShiftCoordinates_unshift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma sixVertexBetheShiftCoordinates_unshift_eq
  {n : Nat}
  {N : Nat}
-- given
  (q : Fin (n + 1) -> Int) :
-- imply
  sixVertexBetheShiftCoordinates N (sixVertexBetheUnshiftCoordinates N q) = q := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheShiftCoordinates_unshift N q

/--
[sixVertexBetheUnshiftCoordinates_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma sixVertexBetheUnshiftCoordinates_shift_eq
  {n : Nat}
  {N : Nat}
-- given
  (r : Fin (n + 1) -> Int) :
-- imply
  sixVertexBetheUnshiftCoordinates N (sixVertexBetheShiftCoordinates N r) = r := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheUnshiftCoordinates_shift N r

/--
[mem_sixVertexBetheInteriorSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma mem_sixVertexBetheInteriorSet_eq
  {n : Nat}
  {N : Nat}
  {i : Fin (n + 1)}
-- given
  (x q : Fin (n + 1) -> Int) :
-- imply
  i ∈ sixVertexBetheInteriorSet N x q ↔ q i ≠ sixVertexBetheShiftCoordinates N x i ∧ q i ≠ x i := by
-- proof
  apply StatMech.FrontierD.mem_sixVertexBetheInteriorSet N x q i

/--
[mem_sixVertexBetheNonnegativeTuples](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma mem_sixVertexBetheNonnegativeTuples_eq
  {n : Nat}
  {N : Nat}
-- given
  (x q : Fin (n + 1) -> Int) :
-- imply
  q ∈ sixVertexBetheNonnegativeTuples N x ↔ q ∈ sixVertexBetheCyclicIntervalTuples N x ∧ sixVertexBetheCollisionSet N x q = ∅ ∧ 0 ≤ q 0 := by
-- proof
  apply StatMech.FrontierD.mem_sixVertexBetheNonnegativeTuples N x q

/--
[mem_sixVertexBetheNegativeTuples](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma mem_sixVertexBetheNegativeTuples_eq
  {n : Nat}
  {N : Nat}
-- given
  (x q : Fin (n + 1) -> Int) :
-- imply
  q ∈ sixVertexBetheNegativeTuples N x ↔ q ∈ sixVertexBetheCyclicIntervalTuples N x ∧ sixVertexBetheCollisionSet N x q = ∅ ∧ q 0 < 0 := by
-- proof
  apply StatMech.FrontierD.mem_sixVertexBetheNegativeTuples N x q

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.physicalCyclicIntervalExpansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma physicalCyclicIntervalExpansion_eq
  {c : Real}
  {N n : Nat}
  {x : SixVertexSector N (n + 1)}
-- given
  (hc : 2 < c)
  (p : Fin (n + 1) -> Real)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p) :
-- imply
  (sixVertexSectorTransferComplex N (n + 1) c).mulVec (sixVertexCoordinateBetheWave c p) x = ∑ q ∈ sixVertexBetheCollisionFreeTuples N (sixVertexSectorIntCoordinates x), sixVertexBetheTupleWaveWeight N c p (sixVertexSectorIntCoordinates x) q := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.physicalCyclicIntervalExpansion hc p hp x

/--
[sixVertexBetheShiftCoordinates_lt_sector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma sixVertexBetheShiftCoordinates_lt_sector_eq
  {N n : Nat}
  {x : SixVertexSector N (n + 1)}
  {i : Fin (n + 1)} :
-- imply
  sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates x) i < sixVertexSectorIntCoordinates x i := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheShiftCoordinates_lt_sector x i

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.physicalWordExpansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma physicalWordExpansion_eq
  {c : Real}
  {N n : Nat}
-- given
  (hc : 2 < c)
  (p : Fin (n + 1) -> Real)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
  (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1) :
-- imply
  SixVertexPhysicalWordExpansion (N := N) c p := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.physicalWordExpansion hc p hp hphase

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.physicalCoordinateBetheEigenrelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean)
-/
@[path]
private lemma physicalCoordinateBetheEigenrelation_eq
  {c : Real}
  {N n : Nat}
-- given
  (hc : 2 < c)
  (p : Fin (n + 1) -> Real)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
  (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1) :
-- imply
  SixVertexCoordinateBetheEigenrelation (N := N) c p := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.physicalCoordinateBetheEigenrelation hc p hp hphase


-- created on 2026-10-23
