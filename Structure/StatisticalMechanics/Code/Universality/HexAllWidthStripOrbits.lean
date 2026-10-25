/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits.Part4


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

structure HexFiniteStripGeometricOrbitData
    {I K V : Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K] [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    (P : D.InteriorPairing) where
  heading : V → Fin 3 → ℤ
  hgeom : ∀ v j,
    D.mid v j - D.pos v = (1 / 2 : ℂ) * hexUnit (heading v j)
  startIncidence : HexIncidence V
  start_mid : D.mid startIncidence.vtx startIncidence.edge = R.start
  start_heading : heading startIncidence.vtx startIncidence.edge = 4
  neg : I → HexIncidence V
  pos : I → HexIncidence V
  pair_ne : ∀ i, neg i ≠ pos i
  midpoint_reflect : ∀ i,
    D.mid (pos i).vtx (pos i).edge =
      hsc_refl R.start h0 (D.mid (neg i).vtx (neg i).edge)
  fixed : K → HexIncidence V
  fixed_reflect : ∀ k,
    D.mid (fixed k).vtx (fixed k).edge =
      hsc_refl R.start h0 (D.mid (fixed k).vtx (fixed k).edge)
  orbitPiece : I ⊕ K → Finset (HexIncidence V)
  pair_piece : ∀ i, orbitPiece (.inl i) = {neg i, pos i}
  fixed_piece : ∀ k, orbitPiece (.inr k) = {fixed k}
  boundary_partition :
    D.incidences \ P.interior =
      {startIncidence} ∪ Finset.univ.biUnion orbitPiece
  start_orbits_disjoint :
    Disjoint ({startIncidence} : Finset (HexIncidence V))
      (Finset.univ.biUnion orbitPiece)
  orbits_disjoint :
    ((Finset.univ : Finset (I ⊕ K)) : Set (I ⊕ K)).PairwiseDisjoint
      orbitPiece


end
end StatMech.Universality
