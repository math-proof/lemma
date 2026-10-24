import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingTorusSparseGreenDecay
open Filter Finset Set StatMech StatMech.FrontierA


/--
[sparseAxisDifference_not_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSparseGreenDecay.lean)
-/
@[path]
private lemma sparseAxisDifference_not_mem_box_eq
  {d : Nat}
  {i : Fin d}
  {R spacing a b : Nat}
-- given
  (hspacing : R < spacing)
  (hab : a ≠ b) :
-- imply
  Pi.single i (((b * spacing : Nat) : Int) - ((a * spacing : Nat) : Int)) ∉ box d R := by
-- proof
  apply StatMech.FrontierA.sparseAxisDifference_not_mem_box i R spacing a b hspacing hab

/--
[isingTorusSparseGreenAverage_eventually_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSparseGreenDecay.lean)
-/
@[path]
private lemma isingTorusSparseGreenAverage_eventually_le_eq
  {d : Nat}
  {delta : Real}
-- given
  (hd : 2 < d)
  (hdelta : 0 < delta) :
-- imply
  ∃ M : Real, 0 ≤ M ∧ ∃ R : Nat, ∀ (i : Fin d) (spacing count : Nat), R < spacing → 0 < count → ∀ᶠ k : Nat in atTop, finiteTorusBlockDifferenceAverage (finiteTorusZeroModeGreen (isingTorusCharacterDispersion (d := d) (k := k))) (isingTorusSparseAxisBlock i spacing count) ≤ M / count + delta := by
-- proof
  apply StatMech.FrontierA.isingTorusSparseGreenAverage_eventually_le hd delta hdelta

/--
[isingTorusZeroMode_eventually_small_subcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSparseGreenDecay.lean)
-/
@[path]
private lemma isingTorusZeroMode_eventually_small_subcritical_eq
  {d : Nat}
  {beta : Real}
  {epsilon : Real}
-- given
  (hd : 2 ≤ d)
  (hbeta : 0 ≤ beta)
  (hlt : beta < IsingFK.betaC (StatMech.Ising.magnetization d))
  (hepsilon : 0 < epsilon) :
-- imply
  ∀ᶠ k : Nat in atTop, (finiteTorusFourierCoeff (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re / Fintype.card (IsingDyadicTorus d k) < epsilon := by
-- proof
  apply StatMech.FrontierA.isingTorusZeroMode_eventually_small_subcritical hd beta hbeta hlt epsilon hepsilon


-- created on 2026-10-23
