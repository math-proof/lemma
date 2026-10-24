import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingTorusAxisBlockAverage
open Finset Set StatMech StatMech.FrontierA


/--
[le_finiteTorusBlockDifferenceAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma le_finiteTorusBlockDifferenceAverage_eq
  [AddCommGroup Gamma]
  {G : Gamma → Real}
  {B : Finset Gamma}
  {m : Real}
-- given
  (hB : B.Nonempty)
  (hm : ∀ a ∈ B, ∀ b ∈ B, m ≤ G (b - a)) :
-- imply
  m ≤ finiteTorusBlockDifferenceAverage G B := by
-- proof
  apply StatMech.FrontierA.le_finiteTorusBlockDifferenceAverage G B m hB hm

/--
[finiteTorusBlockDifferenceAverage_zeroModeGreen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma finiteTorusBlockDifferenceAverage_zeroModeGreen_eq
  [AddCommGroup Gamma]
  [Fintype Gamma]
  {dispersion : AddChar Gamma Complex → Real}
  {B : Finset Gamma} :
-- imply
  finiteTorusBlockDifferenceAverage (finiteTorusZeroModeGreen dispersion) B = (1 / Fintype.card Gamma : Real) * ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex), (dispersion chi)⁻¹ * finiteTorusBlockCharacterWeight B chi := by
-- proof
  apply StatMech.FrontierA.finiteTorusBlockDifferenceAverage_zeroModeGreen dispersion B

/--
[finiteTorusZeroModeGreen_isingSiteToDyadicTorus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma finiteTorusZeroModeGreen_isingSiteToDyadicTorus_eq
  [AddCommGroup Gamma]
  {d k : Nat}
  {x : StatMech.Lattice.Site d} :
-- imply
  finiteTorusZeroModeGreen (isingTorusCharacterDispersion (d := d) (k := k)) (isingSiteToDyadicTorus k x) = isingDyadicTorusGreen x k := by
-- proof
  apply StatMech.FrontierA.finiteTorusZeroModeGreen_isingSiteToDyadicTorus x

/--
[finiteTorusZeroModeGreen_axisDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma finiteTorusZeroModeGreen_axisDifference_eq
  [AddCommGroup Gamma]
  {d k : Nat}
  {i : Fin d}
  {a b : Nat} :
-- imply
  finiteTorusZeroModeGreen (isingTorusCharacterDispersion (d := d) (k := k)) (isingTorusCoordinateShift i b - isingTorusCoordinateShift i a) = isingDyadicTorusGreen (Pi.single i ((b : Int) - (a : Int))) k := by
-- proof
  apply StatMech.FrontierA.finiteTorusZeroModeGreen_axisDifference i a b

/--
[isingTorusCoordinateShift_injectiveOn_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma isingTorusCoordinateShift_injectiveOn_range_eq
  [AddCommGroup Gamma]
  {d k : Nat}
  {i : Fin d}
  {r : Nat}
-- given
  (hr : r < isingDyadicSide k) :
-- imply
  Set.InjOn (isingTorusCoordinateShift (k := k) i) (Finset.range (r + 1) : Set Nat) := by
-- proof
  apply StatMech.FrontierA.isingTorusCoordinateShift_injectiveOn_range i r hr

/--
[isingTorusAxisSegment_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma isingTorusAxisSegment_card_eq
  [AddCommGroup Gamma]
  {d k : Nat}
  {i : Fin d}
  {r : Nat}
-- given
  (hr : r < isingDyadicSide k) :
-- imply
  (isingTorusAxisSegment (k := k) i r).card = r + 1 := by
-- proof
  apply StatMech.FrontierA.isingTorusAxisSegment_card i r hr

/--
[finiteTorusBlockDifferenceAverage_zeroModeGreen_axisSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma finiteTorusBlockDifferenceAverage_zeroModeGreen_axisSegment_eq
  [AddCommGroup Gamma]
  {d k : Nat}
  {i : Fin d}
  {r : Nat}
-- given
  (hr : r < isingDyadicSide k) :
-- imply
  finiteTorusBlockDifferenceAverage (finiteTorusZeroModeGreen (isingTorusCharacterDispersion (d := d) (k := k))) (isingTorusAxisSegment i r) = (1 / ((r + 1 : Nat) : Real) ^ 2) * ∑ a ∈ Finset.range (r + 1), ∑ b ∈ Finset.range (r + 1), isingDyadicTorusGreen (Pi.single i ((b : Int) - (a : Int))) k := by
-- proof
  apply StatMech.FrontierA.finiteTorusBlockDifferenceAverage_zeroModeGreen_axisSegment i r hr

/--
[isingTorusAxisSegment_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma isingTorusAxisSegment_nonempty_eq
  [AddCommGroup Gamma]
  {d k : Nat}
  {i : Fin d}
  {r : Nat} :
-- imply
  (isingTorusAxisSegment (k := k) i r).Nonempty := by
-- proof
  apply StatMech.FrontierA.isingTorusAxisSegment_nonempty i r

/--
[isingTorusSparseAxisBlock_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma isingTorusSparseAxisBlock_nonempty_eq
  [AddCommGroup Gamma]
  {d k : Nat}
  {i : Fin d}
  {spacing count : Nat}
-- given
  (hcount : 0 < count) :
-- imply
  (isingTorusSparseAxisBlock (k := k) i spacing count).Nonempty := by
-- proof
  apply StatMech.FrontierA.isingTorusSparseAxisBlock_nonempty i spacing count hcount

/--
[isingTorusSparseAxisBlock_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma isingTorusSparseAxisBlock_card_eq
  [AddCommGroup Gamma]
  {d k : Nat}
  {i : Fin d}
  {spacing count : Nat}
-- given
  (hspacing : 0 < spacing)
  (hr : (count - 1) * spacing < isingDyadicSide k) :
-- imply
  (isingTorusSparseAxisBlock (k := k) i spacing count).card = count := by
-- proof
  apply StatMech.FrontierA.isingTorusSparseAxisBlock_card i spacing count hspacing hr

/--
[finiteTorusBlockDifferenceAverage_zeroModeGreen_sparseAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma finiteTorusBlockDifferenceAverage_zeroModeGreen_sparseAxis_eq
  [AddCommGroup Gamma]
  {d k : Nat}
  {i : Fin d}
  {spacing count : Nat}
-- given
  (hspacing : 0 < spacing)
  (hr : (count - 1) * spacing < isingDyadicSide k) :
-- imply
  finiteTorusBlockDifferenceAverage (finiteTorusZeroModeGreen (isingTorusCharacterDispersion (d := d) (k := k))) (isingTorusSparseAxisBlock i spacing count) = (1 / (count : Real) ^ 2) * ∑ a ∈ Finset.range count, ∑ b ∈ Finset.range count, isingDyadicTorusGreen (Pi.single i (((b * spacing : Nat) : Int) - ((a * spacing : Nat) : Int))) k := by
-- proof
  apply StatMech.FrontierA.finiteTorusBlockDifferenceAverage_zeroModeGreen_sparseAxis i spacing count hspacing hr

/--
[finiteTorusBlockDifferenceAverage_zeroModeGreen_sparseAxis_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma finiteTorusBlockDifferenceAverage_zeroModeGreen_sparseAxis_le_eq
  [AddCommGroup Gamma]
  {d k : Nat}
  {i : Fin d}
  {spacing count : Nat}
  {M epsilon : Real}
-- given
  (hspacing : 0 < spacing)
  (hcount : 0 < count)
  (hr : (count - 1) * spacing < isingDyadicSide k)
  (hepsilon : 0 ≤ epsilon)
  (hzero : |isingDyadicTorusGreen (0 : StatMech.Lattice.Site d) k| ≤ M)
  (hoff : ∀ a ∈ Finset.range count, ∀ b ∈ Finset.range count, a ≠ b → |isingDyadicTorusGreen (Pi.single i (((b * spacing : Nat) : Int) - ((a * spacing : Nat) : Int))) k| ≤ epsilon) :
-- imply
  finiteTorusBlockDifferenceAverage (finiteTorusZeroModeGreen (isingTorusCharacterDispersion (d := d) (k := k))) (isingTorusSparseAxisBlock i spacing count) ≤ M / count + epsilon := by
-- proof
  apply StatMech.FrontierA.finiteTorusBlockDifferenceAverage_zeroModeGreen_sparseAxis_le i spacing count hspacing hcount hr M epsilon hepsilon hzero hoff

/--
[isingTorusTwoPoint_axis_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma isingTorusTwoPoint_axis_antitone_eq
  [AddCommGroup Gamma]
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
  {a b : Nat}
-- given
  (hbeta : 0 ≤ beta)
  (hab : a ≤ b)
  (hb : b ≤ 2 ^ (k + 1)) :
-- imply
  isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i b) ≤ isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i a) := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_axis_antitone i beta hbeta hab hb

/--
[isingTorusTwoPoint_axisEndpoint_le_difference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma isingTorusTwoPoint_axisEndpoint_le_difference_eq
  [AddCommGroup Gamma]
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
  {r : Nat}
  {a b : Nat}
-- given
  (hbeta : 0 ≤ beta)
  (hr : r ≤ 2 ^ (k + 1))
  (ha : a < r + 1)
  (hb : b < r + 1) :
-- imply
  isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i r) ≤ isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i b - isingTorusCoordinateShift i a) := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_axisEndpoint_le_difference i beta hbeta r hr ha hb

/--
[isingTorusTwoPoint_sparseAxisEndpoint_le_difference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma isingTorusTwoPoint_sparseAxisEndpoint_le_difference_eq
  [AddCommGroup Gamma]
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
  {spacing count : Nat}
  {a b : Nat}
-- given
  (hbeta : 0 ≤ beta)
  (hcount : 0 < count)
  (hr : (count - 1) * spacing ≤ 2 ^ (k + 1))
  (ha : a < count)
  (hb : b < count) :
-- imply
  isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i ((count - 1) * spacing)) ≤ isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i (b * spacing) - isingTorusCoordinateShift i (a * spacing)) := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_sparseAxisEndpoint_le_difference i beta hbeta spacing count hcount hr ha hb

/--
[isingTorusTwoPoint_axisEndpoint_le_greenBlockAverage_of_block](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma isingTorusTwoPoint_axisEndpoint_le_greenBlockAverage_of_block_eq
  [AddCommGroup Gamma]
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
  {r : Nat}
  {B : Finset (IsingDyadicTorus d k)}
-- given
  (hbeta : 0 < beta)
  (hB : B.Nonempty)
  (hlower : ∀ a ∈ B, ∀ b ∈ B, isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i r) ≤ isingTorusTwoPoint (k := k) beta 0 (b - a)) :
-- imply
  isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i r) ≤ (finiteTorusFourierCoeff (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re / Fintype.card (IsingDyadicTorus d k) + (1 / beta) * finiteTorusBlockDifferenceAverage (finiteTorusZeroModeGreen (Gamma := IsingDyadicTorus d k) (isingTorusCharacterDispersion (d := d) (k := k))) B := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_axisEndpoint_le_greenBlockAverage_of_block i beta hbeta r B hB hlower

/--
[isingTorusTwoPoint_sparseAxisEndpoint_le_greenBlockAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma isingTorusTwoPoint_sparseAxisEndpoint_le_greenBlockAverage_eq
  [AddCommGroup Gamma]
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
  {spacing count : Nat}
-- given
  (hbeta : 0 < beta)
  (hcount : 0 < count)
  (hr : (count - 1) * spacing ≤ 2 ^ (k + 1)) :
-- imply
  isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i ((count - 1) * spacing)) ≤ (finiteTorusFourierCoeff (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re / Fintype.card (IsingDyadicTorus d k) + (1 / beta) * finiteTorusBlockDifferenceAverage (finiteTorusZeroModeGreen (Gamma := IsingDyadicTorus d k) (isingTorusCharacterDispersion (d := d) (k := k))) (isingTorusSparseAxisBlock (k := k) i spacing count) := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_sparseAxisEndpoint_le_greenBlockAverage i beta hbeta spacing count hcount hr

/--
[isingTorusTwoPoint_axisEndpoint_le_blockDifferenceAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma isingTorusTwoPoint_axisEndpoint_le_blockDifferenceAverage_eq
  [AddCommGroup Gamma]
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
  {r : Nat}
-- given
  (hbeta : 0 ≤ beta)
  (hr : r ≤ 2 ^ (k + 1)) :
-- imply
  isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i r) ≤ finiteTorusBlockDifferenceAverage (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) (isingTorusAxisSegment i r) := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_axisEndpoint_le_blockDifferenceAverage i beta hbeta r hr

/--
[isingTorusTwoPoint_axisEndpoint_le_fourierBlockBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma isingTorusTwoPoint_axisEndpoint_le_fourierBlockBound_eq
  [AddCommGroup Gamma]
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
  {r : Nat}
-- given
  (hbeta : 0 < beta)
  (hr : r ≤ 2 ^ (k + 1)) :
-- imply
  isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i r) ≤ (finiteTorusFourierCoeff (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re / Fintype.card (IsingDyadicTorus d k) + (1 / Fintype.card (IsingDyadicTorus d k) : Real) * ∑ chi ∈ Finset.univ.erase (0 : AddChar (IsingDyadicTorus d k) Complex), ((1 / beta) / isingTorusCharacterDispersion chi) * finiteTorusBlockCharacterWeight (isingTorusAxisSegment i r) chi := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_axisEndpoint_le_fourierBlockBound i beta hbeta r hr

/--
[isingTorusTwoPoint_axisEndpoint_le_greenBlockAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean)
-/
@[path]
private lemma isingTorusTwoPoint_axisEndpoint_le_greenBlockAverage_eq
  [AddCommGroup Gamma]
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
  {r : Nat}
-- given
  (hbeta : 0 < beta)
  (hr : r ≤ 2 ^ (k + 1)) :
-- imply
  isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i r) ≤ (finiteTorusFourierCoeff (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re / Fintype.card (IsingDyadicTorus d k) + (1 / beta) * finiteTorusBlockDifferenceAverage (finiteTorusZeroModeGreen (Gamma := IsingDyadicTorus d k) (isingTorusCharacterDispersion (d := d) (k := k))) (isingTorusAxisSegment (k := k) i r) := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_axisEndpoint_le_greenBlockAverage i beta hbeta r hr


-- created on 2026-10-23
