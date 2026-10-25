import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareCaratheodory.Part5
open StatMech StatMech.Universality


/--
[exists_fkIsingSquareWiredCarrier_scaledPosition_near](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareCaratheodory.lean)
-/
@[path]
private lemma exists_fkIsingSquareWiredCarrier_scaledPosition_near_eq
  {n : Nat}
  {scale : Real}
  {z : Complex}
-- given
  (hn : 0 < n)
  (hscale : 0 < scale)
  (hx0 : -(n : Int) ≤ ⌊z.re / scale⌋)
  (hx1 : ⌊z.re / scale⌋ < (n : Int))
  (hy0 : -(n : Int) ≤ ⌊z.im / scale⌋)
  (hy1 : ⌊z.im / scale⌋ ≤ (n : Int)) :
-- imply
  ∃ a : FKIsingSquareWiredCarrier n, dist z ((scale : Complex) * fkIsingSquareWiredCarrierPosition n hn a) < 3 * scale := by
-- proof
  apply StatMech.Universality.exists_fkIsingSquareWiredCarrier_scaledPosition_near n hn scale hscale z hx0 hx1 hy0 hy1

/--
[fkIsingExpandingSquareSide_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareCaratheodory.lean)
-/
@[path]
private lemma fkIsingExpandingSquareSide_pos_eq
  {k : Nat} :
-- imply
  0 < fkIsingExpandingSquareSide k := by
-- proof
  apply StatMech.Universality.fkIsingExpandingSquareSide_pos k

/--
[fkIsingExpandingSquareScale_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareCaratheodory.lean)
-/
@[path]
private lemma fkIsingExpandingSquareScale_pos_eq
  {k : Nat} :
-- imply
  0 < fkIsingExpandingSquareScale k := by
-- proof
  apply StatMech.Universality.fkIsingExpandingSquareScale_pos k

/--
[fkIsingExpandingSquareMesh_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareCaratheodory.lean)
-/
@[path]
private lemma fkIsingExpandingSquareMesh_pos_eq
  {k : Nat} :
-- imply
  0 < fkIsingExpandingSquareMesh k := by
-- proof
  apply StatMech.Universality.fkIsingExpandingSquareMesh_pos k

/--
[fkIsingExpandingSquareMesh_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareCaratheodory.lean)
-/
@[path]
private lemma fkIsingExpandingSquareMesh_tendsto_zero_eq :
-- imply
  Tendsto fkIsingExpandingSquareMesh atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingSquareMesh_tendsto_zero

/--
[fkIsingExpandingSquare_compact_eventually_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareCaratheodory.lean)
-/
@[path]
private lemma fkIsingExpandingSquare_compact_eventually_mem_eq
  {K : Set Complex}
-- given
  (hK : IsCompact K) :
-- imply
  ∀ᶠ k in atTop, K ⊆ fkIsingExpandingSquareCarrier k := by
-- proof
  apply StatMech.Universality.fkIsingExpandingSquare_compact_eventually_mem K hK

/--
[fkIsingSquareRadialPatchWindowCarrier_scaledPosition_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareCaratheodory.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchWindowCarrier_scaledPosition_norm_le_eq
  {n m baseI baseJ R : Nat}
  {p : IsingLeapfrogBox R}
-- given
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m) :
-- imply
  ‖((1 / (m : Real) : Real) : Complex) * fkIsingSquareWiredCarrierPosition n (by omega) (fkIsingSquareRadialPatchWindowCarrier n m baseI baseJ R hm hfitI hfitJ p)‖ ≤ 3 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchWindowCarrier_scaledPosition_norm_le n m baseI baseJ R hm hm2 hfitI hfitJ p

/--
[fkIsingExpandingSquareRadialSupport_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareCaratheodory.lean)
-/
@[path]
private lemma fkIsingExpandingSquareRadialSupport_nonempty_eq
  {k : Nat} :
-- imply
  (fkIsingExpandingSquareRadialSupport k).Nonempty := by
-- proof
  apply StatMech.Universality.fkIsingExpandingSquareRadialSupport_nonempty k

/--
[fkIsingExpandingSquareRadialSupport_mem_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareCaratheodory.lean)
-/
@[path]
private lemma fkIsingExpandingSquareRadialSupport_mem_closedBall_eq
  {k : Nat}
  {a : fkIsingExpandingSquareCaratheodoryApproximation.M k}
-- given
  (hk : k ≠ 0)
  (ha : a ∈ fkIsingExpandingSquareRadialSupport k) :
-- imply
  dist (fkIsingExpandingSquareCaratheodoryApproximation.medialEmbedding k a) 0 ≤ 4 := by
-- proof
  apply StatMech.Universality.fkIsingExpandingSquareRadialSupport_mem_closedBall k a hk ha

/--
[fkIsingExpandingSquareRadialSupport_hasEventualCompactWindowDiameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareCaratheodory.lean)
-/
@[path]
private lemma fkIsingExpandingSquareRadialSupport_hasEventualCompactWindowDiameter_eq :
-- imply
  FKIsingCaratheodoryApproximation.HasEventualCompactWindowDiameter fkIsingExpandingSquareCaratheodoryApproximation fkIsingExpandingSquareRadialSupport := by
-- proof
  apply StatMech.Universality.fkIsingExpandingSquareRadialSupport_hasEventualCompactWindowDiameter


-- created on 2026-10-23
