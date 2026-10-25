/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexPairedBoundaryNormalized
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection.Part2


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators


structure HexFiniteStripReflectedPairing
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (C : HexFiniteStripBoundaryCore R h0 D P) where
  heading : V → Fin 3 → ℤ
  hgeom : ∀ v j,
    D.mid v j - D.pos v = (1 / 2 : ℂ) * hexUnit (heading v j)
  startIncidence : HexIncidence V
  start_mid : D.mid startIncidence.vtx startIncidence.edge = R.start
  start_heading : heading startIncidence.vtx startIncidence.edge = 4
  neg : ι → HexIncidence V
  pos : ι → HexIncidence V
  pair_ne : ∀ i, neg i ≠ pos i
  headNeg : ι → ℤ
  headPos : ι → ℤ
  hHeadNeg : ∀ i, heading (neg i).vtx (neg i).edge = headNeg i
  hHeadPos : ∀ i, heading (pos i).vtx (pos i).edge = headPos i
  midpoint_reflect : ∀ i,
    D.mid (pos i).vtx (pos i).edge =
      hsc_refl R.start h0 (D.mid (neg i).vtx (neg i).edge)
  region_reflect : ∀ m, R.inRegion m →
    R.inRegion (hsc_refl R.start h0 m)
  winding : ι → ℝ
  winding_neg : ∀ i ts,
    (ofTurns R.start h0 ts).IsLegalSAW ∧
        (ofTurns R.start h0 ts).StaysIn R.inRegion ∧
        (ofTurns R.start h0 ts).EndsAt
          (D.mid (neg i).vtx (neg i).edge) →
      (ofTurns R.start h0 ts).turning = winding i
  tilt_reflect : ∀ i,
    hexPhase_sideTilt (headPos i) = -hexPhase_sideTilt (headNeg i)
  boundary_partition :
    D.incidences \ P.interior =
      {startIncidence} ∪ Finset.univ.biUnion (fun i ↦ {neg i, pos i})
  start_pairs_disjoint :
    Disjoint ({startIncidence} : Finset (HexIncidence V))
      (Finset.univ.biUnion (fun i ↦ {neg i, pos i}))
  pairs_disjoint :
    ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      (fun i ↦ ({neg i, pos i} : Finset (HexIncidence V)))

end StatMech.Universality
