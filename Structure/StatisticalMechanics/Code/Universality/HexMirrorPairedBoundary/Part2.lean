/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexGenuineStripPhaseObstruction
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairedBoundary


namespace StatMech.Universality

open Complex Set

open scoped BigOperators


structure HexFiniteStripMirrorPairedData
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
  pairs : ι → HexMirrorBoundaryPair D heading
  boundary_partition :
    D.incidences \ P.interior =
      {startIncidence} ∪ Finset.univ.biUnion (fun i => (pairs i).piece)
  start_pairs_disjoint :
    Disjoint ({startIncidence} : Finset (HexIncidence V))
      (Finset.univ.biUnion (fun i => (pairs i).piece))
  pairs_disjoint :
    ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      (fun i => (pairs i).piece)

end StatMech.Universality
