import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.HexagonalTranslatedArm
open Finset Set Filter Topology MeasureTheory SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[hexagonalTransBox_mem_bufferLevel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalTranslatedArm.lean)
-/
@[path]
private lemma hexagonalTransBox_mem_bufferLevel_eq
  {k : Nat}
  {x : Site 2}
  {y : HexagonalTransBoxVertex (2 * k) x} :
-- imply
  y.1.1 ∈ box 2 (hexagonalTransBufferLevel k x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransBox_mem_bufferLevel k x y

/--
[hexagonalTransBoxToBuffered_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalTranslatedArm.lean)
-/
@[path]
private lemma hexagonalTransBoxToBuffered_injective_eq
  {k : Nat}
  {x : Site 2} :
-- imply
  Function.Injective (hexagonalTransBoxToBuffered k x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransBoxToBuffered_injective k x

/--
[hexagonalTransBoxToBufferedAt_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalTranslatedArm.lean)
-/
@[path]
private lemma hexagonalTransBoxToBufferedAt_injective_eq
  {k : Nat}
  {x : Site 2}
  {m : Nat}
-- given
  (hm : hexagonalTransBufferLevel k x ≤ m) :
-- imply
  Function.Injective (hexagonalTransBoxToBufferedAt k x m hm) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransBoxToBufferedAt_injective k x m hm

/--
[hexagonalTransBoxToBufferedAt_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalTranslatedArm.lean)
-/
@[path]
private lemma hexagonalTransBoxToBufferedAt_adjMatch_eq
  {k : Nat}
  {x : Site 2}
  {m : Nat}
-- given
  (hm : hexagonalTransBufferLevel k x ≤ m) :
-- imply
  ocd_AdjMatch (hexagonalTransBoxGraph (2 * k) x) (hexagonal.bufferedGraph m) (hexagonalTransBoxToBufferedAt k x m hm) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransBoxToBufferedAt_adjMatch k x m hm

/--
[hexagonalTransBoxToBufferedAt_inducedWiring_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalTranslatedArm.lean)
-/
@[path]
private lemma hexagonalTransBoxToBufferedAt_inducedWiring_le_eq
  {k : Nat}
  {x : Site 2}
  {m : Nat}
  {psi : ConfigSpace (Sym2 (hexagonal.BufferedVertex m))}
-- given
  (hk : 1 ≤ k)
  (hm : hexagonalTransBufferLevel k x < m) :
-- imply
  ocd_inducedWiring (hexagonal.bufferedGraph m) (hexagonalTransBoxToBufferedAt k x m hm.le) (hexagonal.bufferedBoundary m) psi ≤ boundaryCliqueGraph (hexagonalTransBoxBoundary (2 * k) x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransBoxToBufferedAt_inducedWiring_le k hk x m hm psi

/--
[hexagonalTransShellFullEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalTranslatedArm.lean)
-/
@[path]
private lemma hexagonalTransShellFullEvent_increasing_eq
  {R k : Nat}
  {x : HexVertex} :
-- imply
  IsIncreasing (hexagonalTransShellFullEvent R k x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransShellFullEvent_increasing R k x

/--
[hexagonalBufferedTransShellEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalTranslatedArm.lean)
-/
@[path]
private lemma hexagonalBufferedTransShellEvent_increasing_eq
  {k : Nat}
  {x : HexVertex} :
-- imply
  IsIncreasing (hexagonalBufferedTransShellEvent k x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBufferedTransShellEvent_increasing k x

/--
[hexagonalTransFullMass_eq_outerInnerTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalTranslatedArm.lean)
-/
@[path]
private lemma hexagonalTransFullMass_eq_outerInnerTheta_eq
  {k : Nat}
  {x : HexVertex}
  {q beta : Real}
-- given
  (hk : 1 ≤ k)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  finiteWiredEventMass (hexagonalTransBoxGraph (2 * k) x.1) (hexagonalTransBoxBoundary (2 * k) x.1) (1 - Real.exp (-beta)) q (hexagonalTransShellFullEvent (2 * k) k x) = hexagonalOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransFullMass_eq_outerInnerTheta k hk x q beta hq hbeta

/--
[hexagonalBufferedTransShell_finite_le_theta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalTranslatedArm.lean)
-/
@[path]
private lemma hexagonalBufferedTransShell_finite_le_theta_eq
  {k : Nat}
  {x : HexVertex}
  {m : Nat}
  {q beta : Real}
-- given
  (hk : 1 ≤ k)
  (hm : hexagonalTransBufferLevel k x.1 < m)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  (hexagonal.wiredBufferedMeasure m (by rw [sub_pos] exact Real.exp_lt_one_iff.mpr (by linarith)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real (hexagonal.bufferedCylinder (hexagonalTransBufferLevel k x.1) (hexagonalBufferedTransShellEvent k x)) ≤ hexagonalOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBufferedTransShell_finite_le_theta k hk x m hm q beta hq hbeta

/--
[hexagonalBufferedTransShell_infinite_le_theta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalTranslatedArm.lean)
-/
@[path]
private lemma hexagonalBufferedTransShell_infinite_le_theta_eq
  {k : Nat}
  {x : HexVertex}
  {q beta : Real}
-- given
  (hk : 1 ≤ k)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  (hexagonal.wiredBufferedInfiniteVolume (by rw [sub_pos] exact Real.exp_lt_one_iff.mpr (by linarith)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real (hexagonal.bufferedCylinder (hexagonalTransBufferLevel k x.1) (hexagonalBufferedTransShellEvent k x)) ≤ hexagonalOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBufferedTransShell_infinite_le_theta k hk x q beta hq hbeta

/--
[hexagonal_twoPointEvent_subset_transShell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalTranslatedArm.lean)
-/
@[path]
private lemma hexagonal_twoPointEvent_subset_transShell_eq
  {k : Nat}
  {x y : HexVertex}
-- given
  (hk : 1 ≤ k)
  (hxy : k ≤ centeredRadius x.1 y.1) :
-- imply
  hexagonal.twoPointEvent x y ⊆ hexagonal.bufferedCylinder (hexagonalTransBufferLevel k x.1) (hexagonalBufferedTransShellEvent k x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_twoPointEvent_subset_transShell k hk x y hxy


-- created on 2026-10-23
