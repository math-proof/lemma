import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionThermodynamic.Part3
open Filter Topology Set StatMech StatMech.FrontierA


/--
[fixedHeightSurfaceDensity_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean)
-/
@[path]
private lemma fixedHeightSurfaceDensity_tendsto_eq
  {F : Nat → Nat → Real}
  {k : Nat}
-- given
  (hF : ∀ m n, 0 ≤ F m n)
  (hsub : HorizontallySubadditive F) :
-- imply
  Tendsto (fun m : Nat => rectangularSurfaceDensity F m k) atTop (nhds ((hsub k).lim / (k : Real))) := by
-- proof
  apply StatMech.FrontierA.fixedHeightSurfaceDensity_tendsto hF hsub k

/--
[horizontalStripRate_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean)
-/
@[path]
private lemma horizontalStripRate_nonneg_eq
  {F : Nat → Nat → Real}
  {k : Nat}
-- given
  (hF : ∀ m n, 0 ≤ F m n)
  (hh : HorizontallySubadditive F) :
-- imply
  0 ≤ (hh k).lim := by
-- proof
  apply StatMech.FrontierA.horizontalStripRate_nonneg hF hh k

/--
[horizontalStripRate_subadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean)
-/
@[path]
private lemma horizontalStripRate_subadditive_eq
  {F : Nat → Nat → Real}
-- given
  (hF : ∀ m n, 0 ≤ F m n)
  (hh : HorizontallySubadditive F)
  (hv : VerticallySubadditive F) :
-- imply
  Subadditive (fun k => (hh k).lim) := by
-- proof
  apply StatMech.FrontierA.horizontalStripRate_subadditive hF hh hv

/--
[iteratedRectangularSurfaceDensity_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean)
-/
@[path]
private lemma iteratedRectangularSurfaceDensity_tendsto_eq
  {F : Nat → Nat → Real}
-- given
  (hF : ∀ m n, 0 ≤ F m n)
  (hh : HorizontallySubadditive F)
  (hv : VerticallySubadditive F) :
-- imply
  Tendsto (fun k : Nat => (hh k).lim / (k : Real)) atTop (nhds (horizontalStripRate_subadditive hF hh hv).lim) := by
-- proof
  apply StatMech.FrontierA.iteratedRectangularSurfaceDensity_tendsto hF hh hv

/--
[positiveRectangularSurfaceDensities_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean)
-/
@[path]
private lemma positiveRectangularSurfaceDensities_nonempty_eq
  {F : Nat → Nat → Real} :
-- imply
  (positiveRectangularSurfaceDensities F).Nonempty := by
-- proof
  apply StatMech.FrontierA.positiveRectangularSurfaceDensities_nonempty F

/--
[positiveRectangularSurfaceDensities_bddBelow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean)
-/
@[path]
private lemma positiveRectangularSurfaceDensities_bddBelow_eq
  {F : Nat → Nat → Real}
-- given
  (hF : ∀ m n, 0 ≤ F m n) :
-- imply
  BddBelow (positiveRectangularSurfaceDensities F) := by
-- proof
  apply StatMech.FrontierA.positiveRectangularSurfaceDensities_bddBelow hF

/--
[rectangularSurfaceRate_le_density](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean)
-/
@[path]
private lemma rectangularSurfaceRate_le_density_eq
  {F : Nat → Nat → Real}
  {m n : Nat}
-- given
  (hF : ∀ m n, 0 ≤ F m n)
  (hm : 0 < m)
  (hn : 0 < n) :
-- imply
  rectangularSurfaceRate F ≤ rectangularSurfaceDensity F m n := by
-- proof
  apply StatMech.FrontierA.rectangularSurfaceRate_le_density hF hm hn

/--
[rectangularSurfaceRate_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean)
-/
@[path]
private lemma rectangularSurfaceRate_nonneg_eq
  {F : Nat → Nat → Real}
-- given
  (hF : ∀ m n, 0 ≤ F m n) :
-- imply
  0 ≤ rectangularSurfaceRate F := by
-- proof
  apply StatMech.FrontierA.rectangularSurfaceRate_nonneg hF

/--
[exists_rectangularDensity_lt_rate_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean)
-/
@[path]
private lemma exists_rectangularDensity_lt_rate_add_eq
  {F : Nat → Nat → Real}
  {epsilon : Real}
-- given
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ m n : Nat, 0 < m ∧ 0 < n ∧ rectangularSurfaceDensity F m n < rectangularSurfaceRate F + epsilon := by
-- proof
  apply StatMech.FrontierA.exists_rectangularDensity_lt_rate_add F hepsilon

/--
[rectangularSurfaceDensity_tendsto_rate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean)
-/
@[path]
private lemma rectangularSurfaceDensity_tendsto_rate_eq
  {F : Nat → Nat → Real}
-- given
  (hF : ∀ m n, 0 ≤ F m n)
  (hglue : HasRectangularBlockGluing F) :
-- imply
  Tendsto (fun n : Nat => rectangularSurfaceDensity F n n) atTop (nhds (rectangularSurfaceRate F)) := by
-- proof
  apply StatMech.FrontierA.rectangularSurfaceDensity_tendsto_rate hF hglue

/--
[surfaceRate_shape_independent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean)
-/
@[path]
private lemma surfaceRate_shape_independent_eq
  {f g : Nat → Real}
  {tau : Real}
-- given
  (hf : Tendsto f atTop (nhds tau))
  (hboundary : Tendsto (fun n => g n - f n) atTop (nhds 0)) :
-- imply
  Tendsto g atTop (nhds tau) := by
-- proof
  apply StatMech.FrontierA.surfaceRate_shape_independent hf hboundary

/--
[cubicalSquareWilsonFreeEnergy_eq_disorderFreeEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean)
-/
@[path]
private lemma cubicalSquareWilsonFreeEnergy_eq_disorderFreeEnergy_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  cubicalSquareWilsonFreeEnergy beta n = cubicalSquareDisorderFreeEnergy beta n := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilsonFreeEnergy_eq_disorderFreeEnergy hbeta n

/--
[cubicalSquareWilsonDensity_eq_disorderDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean)
-/
@[path]
private lemma cubicalSquareWilsonDensity_eq_disorderDensity_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  cubicalSquareWilsonDensity beta n = cubicalSquareDisorderDensity beta n := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilsonDensity_eq_disorderDensity hbeta n

/--
[cubicalSquareWilsonDensity_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean)
-/
@[path]
private lemma cubicalSquareWilsonDensity_mem_Icc_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  cubicalSquareWilsonDensity beta n ∈ Set.Icc 0 (2 * gaugeDualCoupling beta) := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilsonDensity_mem_Icc hbeta n

/--
[cubicalSquareDisorderDensity_tendsto_iff_wilsonDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean)
-/
@[path]
private lemma cubicalSquareDisorderDensity_tendsto_iff_wilsonDensity_eq
  {beta tau : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  Tendsto (cubicalSquareDisorderDensity beta) atTop (nhds tau) ↔ Tendsto (cubicalSquareWilsonDensity beta) atTop (nhds tau) := by
-- proof
  apply StatMech.FrontierA.cubicalSquareDisorderDensity_tendsto_iff_wilsonDensity hbeta

/--
[exists_cubicalSquareSurfaceRate_subseq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean)
-/
@[path]
private lemma exists_cubicalSquareSurfaceRate_subseq_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  ∃ tau ∈ Set.Icc 0 (2 * gaugeDualCoupling beta), ∃ phi : Nat → Nat, StrictMono phi ∧ Tendsto (cubicalSquareWilsonDensity beta ∘ phi) atTop (nhds tau) ∧ Tendsto (cubicalSquareDisorderDensity beta ∘ phi) atTop (nhds tau) := by
-- proof
  apply StatMech.FrontierA.exists_cubicalSquareSurfaceRate_subseq hbeta


-- created on 2026-10-23
