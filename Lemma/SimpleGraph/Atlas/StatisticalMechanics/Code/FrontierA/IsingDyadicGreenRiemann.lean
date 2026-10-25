import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenRiemann.Part6
open Bornology Filter Finset MeasureTheory Set StatMech StatMech.FrontierA


/--
[isingTorusCenteredMomentumFun_mem_cube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingTorusCenteredMomentumFun_mem_cube_eq
  {d : Nat}
  {k : Nat}
  {p : IsingDyadicTorus d k} :
-- imply
  isingTorusCenteredMomentumFun p ∈ isingNormalizedCoordinateCube d := by
-- proof
  apply StatMech.FrontierA.isingTorusCenteredMomentumFun_mem_cube p

/--
[isingTorusCenteredMomentumFun_mem_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingTorusCenteredMomentumFun_mem_lattice_eq
  {d : Nat}
  {k : Nat}
  {p : IsingDyadicTorus d k} :
-- imply
  isingTorusCenteredMomentumFun p ∈ ((isingDyadicSide k : Real)⁻¹ • isingUnitMomentumLattice d) := by
-- proof
  apply StatMech.FrontierA.isingTorusCenteredMomentumFun_mem_lattice p

/--
[isingTorusMomentumGridEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingTorusMomentumGridEquiv_apply_eq
  {d : Nat}
  {k : Nat}
  {p : IsingDyadicTorus d k} :
-- imply
  (isingTorusMomentumGridEquiv d k p).val = isingTorusCenteredMomentumFun p := by
-- proof
  apply StatMech.FrontierA.isingTorusMomentumGridEquiv_apply p

/--
[isingNormalizedCoordinateDispersion_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingNormalizedCoordinateDispersion_centered_eq
  {d : Nat}
  {k : Nat}
  {p : IsingDyadicTorus d k} :
-- imply
  isingNormalizedCoordinateDispersion (isingTorusCenteredMomentumFun p) = isingTorusCharacterDispersion (isingTorusMomentumChar p) := by
-- proof
  apply StatMech.FrontierA.isingNormalizedCoordinateDispersion_centered p

/--
[isingMomentumChar_site_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingMomentumChar_site_re_eq
  {d : Nat}
  {k : Nat}
  {p : IsingDyadicTorus d k}
  {x : Site d} :
-- imply
  (conj (isingTorusMomentumChar p (isingSiteToDyadicTorus k x))).re = Real.cos (2 * Real.pi * ∑ i : Fin d, isingTorusCenteredMomentumFun p i * (x i : Real)) := by
-- proof
  apply StatMech.FrontierA.isingMomentumChar_site_re p x

/--
[isingDyadicTorus_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingDyadicTorus_card_eq
  {d : Nat}
  {d k : Nat} :
-- imply
  Fintype.card (IsingDyadicTorus d k) = isingDyadicSide k ^ d := by
-- proof
  apply StatMech.FrontierA.isingDyadicTorus_card d k

/--
[isingDyadicTorusGreen_eq_character_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingDyadicTorusGreen_eq_character_sum_eq
  {d : Nat}
  {k : Nat}
  {x : Site d} :
-- imply
  isingDyadicTorusGreen x k = (1 / Fintype.card (IsingDyadicTorus d k) : Real) * ∑ p : IsingDyadicTorus d k, if p = 0 then 0 else (conj (isingTorusMomentumChar p (isingSiteToDyadicTorus k x))).re * (isingTorusCharacterDispersion (isingTorusMomentumChar p))⁻¹ := by
-- proof
  apply StatMech.FrontierA.isingDyadicTorusGreen_eq_character_sum x

/--
[isingNormalizedCoordinateDispersion_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingNormalizedCoordinateDispersion_zero_eq
  {d : Nat} :
-- imply
  isingNormalizedCoordinateDispersion (0 : IsingMomentumCoordinates d) = 0 := by
-- proof
  apply StatMech.FrontierA.isingNormalizedCoordinateDispersion_zero

/--
[isingDyadicTorusGreen_sub_regularized_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingDyadicTorusGreen_sub_regularized_abs_le_eq
  {d : Nat}
  {k M : Nat}
  {eta : Real}
  {x : Fin d → Int}
-- given
  (heta : 0 < eta)
  (hsmall : ∀ p : IsingDyadicTorus d k, p ≠ 0 → isingTorusCharacterDispersion (isingTorusMomentumChar p) < eta → p ∈ isingTorusLowMomentum d k M) :
-- imply
  |isingDyadicTorusGreen x k - isingRegularizedTorusGreen eta x k| ≤ (1 / (isingDyadicSide k : Real) ^ d) * (eta⁻¹ + ∑ p ∈ isingTorusLowMomentum d k M, (isingTorusCharacterDispersion (isingTorusMomentumChar p))⁻¹) := by
-- proof
  apply StatMech.FrontierA.isingDyadicTorusGreen_sub_regularized_abs_le eta heta x hsmall

/--
[isingTorus_smallDispersion_mem_lowMomentum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingTorus_smallDispersion_mem_lowMomentum_eq
  {d : Nat}
  {k : Nat}
  {delta eta : Real}
  {p : IsingDyadicTorus d k}
-- given
  (hdelta : 0 < delta)
  (hdeltaHalf : delta ≤ 1 / 2)
  (heta : eta ≤ 16 * delta ^ 2)
  (hp0 : p ≠ 0)
  (hpeta : isingTorusCharacterDispersion (isingTorusMomentumChar p) < eta) :
-- imply
  p ∈ isingTorusLowMomentum d k ⌈delta * isingDyadicSide k⌉₊ := by
-- proof
  apply StatMech.FrontierA.isingTorus_smallDispersion_mem_lowMomentum delta eta hdelta hdeltaHalf heta p hp0 hpeta

/--
[isingLowMomentumRadius_le_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingLowMomentumRadius_le_half_eq
  {d : Nat}
  {k : Nat}
  {delta : Real}
-- given
  (hdelta : 0 ≤ delta)
  (hdeltaHalf : delta ≤ 1 / 2) :
-- imply
  ⌈delta * isingDyadicSide k⌉₊ ≤ isingDyadicSide k / 2 := by
-- proof
  apply StatMech.FrontierA.isingLowMomentumRadius_le_half delta hdelta hdeltaHalf

/--
[isingRegularizedTorusGreen_eq_grid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingRegularizedTorusGreen_eq_grid_eq
  {d : Nat}
  {eta : Real}
  {x : Fin d → Int}
  {k : Nat} :
-- imply
  isingRegularizedTorusGreen eta x k = isingRegularizedGridGreen eta x (isingDyadicSide k) := by
-- proof
  apply StatMech.FrontierA.isingRegularizedTorusGreen_eq_grid eta x k

/--
[measurableSet_isingNormalizedCoordinateCube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma measurableSet_isingNormalizedCoordinateCube_eq
  {d : Nat}
  {d : Nat} :
-- imply
  MeasurableSet (isingNormalizedCoordinateCube d) := by
-- proof
  apply StatMech.FrontierA.measurableSet_isingNormalizedCoordinateCube d

/--
[isBounded_isingNormalizedCoordinateCube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isBounded_isingNormalizedCoordinateCube_eq
  {d : Nat}
  {d : Nat} :
-- imply
  IsBounded (isingNormalizedCoordinateCube d) := by
-- proof
  apply StatMech.FrontierA.isBounded_isingNormalizedCoordinateCube d

/--
[ordConnected_isingNormalizedCoordinateCube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma ordConnected_isingNormalizedCoordinateCube_eq
  {d : Nat}
  {d : Nat} :
-- imply
  (isingNormalizedCoordinateCube d).OrdConnected := by
-- proof
  apply StatMech.FrontierA.ordConnected_isingNormalizedCoordinateCube d

/--
[volume_frontier_isingNormalizedCoordinateCube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma volume_frontier_isingNormalizedCoordinateCube_eq
  {d : Nat}
  {d : Nat} :
-- imply
  volume (frontier (isingNormalizedCoordinateCube d)) = 0 := by
-- proof
  apply StatMech.FrontierA.volume_frontier_isingNormalizedCoordinateCube d

/--
[continuous_isingNormalizedCoordinateDispersion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma continuous_isingNormalizedCoordinateDispersion_eq
  {d : Nat}
  {d : Nat} :
-- imply
  Continuous (isingNormalizedCoordinateDispersion : IsingMomentumCoordinates d → Real) := by
-- proof
  apply StatMech.FrontierA.continuous_isingNormalizedCoordinateDispersion d

/--
[continuous_isingRegularizedInverseDispersion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma continuous_isingRegularizedInverseDispersion_eq
  {d : Nat}
  {eta : Real}
-- given
  (heta : 0 < eta) :
-- imply
  Continuous (isingRegularizedInverseDispersion eta : IsingMomentumCoordinates d → Real) := by
-- proof
  apply StatMech.FrontierA.continuous_isingRegularizedInverseDispersion eta heta

/--
[continuous_isingRegularizedGreenIntegrand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma continuous_isingRegularizedGreenIntegrand_eq
  {d : Nat}
  {eta : Real}
  {x : Fin d → Int}
-- given
  (heta : 0 < eta) :
-- imply
  Continuous (isingRegularizedGreenIntegrand eta x : IsingMomentumCoordinates d → Real) := by
-- proof
  apply StatMech.FrontierA.continuous_isingRegularizedGreenIntegrand eta heta x

/--
[isingCoordinateFrequency_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingCoordinateFrequency_apply_eq
  {d : Nat}
  {x : Fin d → Int}
  {q : IsingMomentumCoordinates d} :
-- imply
  isingCoordinateFrequency x q = ∑ i : Fin d, q i * (x i : Real) := by
-- proof
  apply StatMech.FrontierA.isingCoordinateFrequency_apply x q

/--
[integrable_isingRegularizedCoordinateDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma integrable_isingRegularizedCoordinateDensity_eq
  {d : Nat}
  {eta : Real}
-- given
  (heta : 0 < eta) :
-- imply
  Integrable (isingRegularizedCoordinateDensity eta : IsingMomentumCoordinates d → Complex) := by
-- proof
  apply StatMech.FrontierA.integrable_isingRegularizedCoordinateDensity eta heta

/--
[isingRegularizedCoordinateGreenComplex_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingRegularizedCoordinateGreenComplex_tendsto_zero_eq
  {d : Nat}
  {eta : Real}
-- given
  (heta : 0 < eta) :
-- imply
  Tendsto (isingRegularizedCoordinateGreenComplex (d := d) eta) (cocompact (StrongDual Real (IsingMomentumCoordinates d))) (nhds 0) := by
-- proof
  apply StatMech.FrontierA.isingRegularizedCoordinateGreenComplex_tendsto_zero eta heta

/--
[isingRegularizedContinuumGreen_eq_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingRegularizedContinuumGreen_eq_re_eq
  {d : Nat}
  {eta : Real}
  {x : Fin d → Int}
-- given
  (heta : 0 < eta) :
-- imply
  isingRegularizedContinuumGreen eta x = (isingRegularizedCoordinateGreenComplex eta (isingCoordinateFrequency x)).re := by
-- proof
  apply StatMech.FrontierA.isingRegularizedContinuumGreen_eq_re eta heta x

/--
[isingCoordinateFrequency_coord_abs_le_norm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingCoordinateFrequency_coord_abs_le_norm_eq
  {d : Nat}
  {x : Fin d → Int}
  {i : Fin d} :
-- imply
  |(x i : Real)| ≤ ‖isingCoordinateFrequency x‖ := by
-- proof
  apply StatMech.FrontierA.isingCoordinateFrequency_coord_abs_le_norm x i

/--
[isingRegularizedContinuumGreen_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingRegularizedContinuumGreen_decay_eq
  {d : Nat}
  {eta : Real}
  {epsilon : Real}
-- given
  (heta : 0 < eta)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ R : Nat, ∀ x : Site d, x ∉ box d R → |isingRegularizedContinuumGreen eta x| < epsilon := by
-- proof
  apply StatMech.FrontierA.isingRegularizedContinuumGreen_decay eta heta epsilon hepsilon

/--
[isingRegularizedGridGreen_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingRegularizedGridGreen_tendsto_eq
  {d : Nat}
  {eta : Real}
  {x : Fin d → Int}
-- given
  (heta : 0 < eta) :
-- imply
  Tendsto (isingRegularizedGridGreen eta x) atTop (nhds (isingRegularizedContinuumGreen eta x)) := by
-- proof
  apply StatMech.FrontierA.isingRegularizedGridGreen_tendsto eta heta x

/--
[isingRegularizedDyadicGridGreen_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingRegularizedDyadicGridGreen_tendsto_eq
  {d : Nat}
  {eta : Real}
  {x : Fin d → Int}
-- given
  (heta : 0 < eta) :
-- imply
  Tendsto (fun k => isingRegularizedGridGreen eta x (isingDyadicSide k)) atTop (nhds (isingRegularizedContinuumGreen eta x)) := by
-- proof
  apply StatMech.FrontierA.isingRegularizedDyadicGridGreen_tendsto eta heta x

/--
[isingRegularizedTorusGreen_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingRegularizedTorusGreen_tendsto_eq
  {d : Nat}
  {eta : Real}
  {x : Fin d → Int}
-- given
  (heta : 0 < eta) :
-- imply
  Tendsto (isingRegularizedTorusGreen eta x) atTop (nhds (isingRegularizedContinuumGreen eta x)) := by
-- proof
  apply StatMech.FrontierA.isingRegularizedTorusGreen_tendsto eta heta x

/--
[isingDyadicTorusGreen_eventually_close_continuum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingDyadicTorusGreen_eventually_close_continuum_eq
  {d : Nat}
  {epsilon : Real}
-- given
  (hd : 2 < d)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ eta : Real, 0 < eta ∧ ∀ x : Site d, ∀ᶠ k : Nat in atTop, |isingDyadicTorusGreen x k - isingRegularizedContinuumGreen eta x| < epsilon := by
-- proof
  apply StatMech.FrontierA.isingDyadicTorusGreen_eventually_close_continuum hd epsilon hepsilon

/--
[isingDyadicTorusGreen_eventually_small_outside_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean)
-/
@[path]
private lemma isingDyadicTorusGreen_eventually_small_outside_box_eq
  {d : Nat}
  {epsilon : Real}
-- given
  (hd : 2 < d)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ R : Nat, ∀ x : Site d, x ∉ box d R → ∀ᶠ k : Nat in atTop, |isingDyadicTorusGreen x k| < epsilon := by
-- proof
  apply StatMech.FrontierA.isingDyadicTorusGreen_eventually_small_outside_box hd epsilon hepsilon


-- created on 2026-10-23
