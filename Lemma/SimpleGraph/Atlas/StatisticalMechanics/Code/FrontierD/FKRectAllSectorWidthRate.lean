import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAllSectorWidthRate
open Filter MeasureTheory Topology StatMech StatMech.FrontierD


/--
[tendsto_fkRectAllSectorNormalization_diagonal_zero_of_freePIMS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAllSectorWidthRate.lean)
-/
@[path]
private lemma tendsto_fkRectAllSectorNormalization_diagonal_zero_of_freePIMS_eq
  {q : Real}
  {r : Nat}
  {m : Nat → Nat}
-- given
  (hq : 4 < q)
  (hperc : let mu := (FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (by linarith : 0 < q)) (fkRectCriticalP_lt_one (by linarith : 0 < q)) (by linarith : 0 < q) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) mu.real (Percolation.percolationEvent 2) = 0)
  (hm : ∀ k, fkRectBoundaryIncidencePIMSHeightLower q r k ≤ m k) :
-- imply
  Tendsto (fun k => -Real.log (fkRectAllSectorNormalization (fkRectFixedChargeVerticalFamily r k (m k)) q) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_fkRectAllSectorNormalization_diagonal_zero_of_freePIMS hq r hperc m hm

/--
[tendsto_fkRectAllSectorNormalizationVerticalRate_zero_of_freePIMS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAllSectorWidthRate.lean)
-/
@[path]
private lemma tendsto_fkRectAllSectorNormalizationVerticalRate_zero_of_freePIMS_eq
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hperc : let mu := (FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (by linarith : 0 < q)) (fkRectCriticalP_lt_one (by linarith : 0 < q)) (by linarith : 0 < q) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) mu.real (Percolation.percolationEvent 2) = 0) :
-- imply
  Tendsto (fkRectAllSectorNormalizationVerticalRate hq r) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_fkRectAllSectorNormalizationVerticalRate_zero_of_freePIMS hq r hperc


-- created on 2026-10-23
