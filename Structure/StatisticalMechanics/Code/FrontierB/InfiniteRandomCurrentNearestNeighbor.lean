/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteRandomCurrentNearestNeighbor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentChainClosure
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FreeCurrentFamilyMixing
import Theorem.StatisticalMechanics.Code.FrontierB.PlusCurrentFamilyMixing.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open Sharpness Ising Lattice Percolation


structure NearestNeighborInfiniteRandomCurrentPackage
    (d : Nat) (beta : Real) (hbeta : 0 < beta) (hd : 1 <= d) : Prop where
  plus_weak : WeakCurrentConverges
    (fun n => plusBoxCurrentMeasure d n beta hbeta.le)
    (infinitePlusCurrentMeasure d beta hbeta.le)
  free_weak : WeakCurrentConverges
    (fun n => freeBoxCurrentMeasure d n beta hbeta.le)
    (infiniteFreeCurrentMeasure d beta hbeta.le)
  plus_invariant : CurrentIsTranslationInvariant
    (H := Multiplicative (Site d))
    (infinitePlusCurrentMeasure d beta hbeta.le :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
  free_invariant : CurrentIsTranslationInvariant
    (H := Multiplicative (Site d))
    (infiniteFreeCurrentMeasure d beta hbeta.le :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
  plus_ergodic : CurrentIsErgodic
    (H := Multiplicative (Site d))
    (infinitePlusCurrentMeasure d beta hbeta.le :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
  free_ergodic : CurrentIsErgodic
    (H := Multiplicative (Site d))
    (infiniteFreeCurrentMeasure d beta hbeta.le :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
  plus_cylinder : forall (S : Finset (Sym2 (Site d)))
      (A : Set (↑S -> Nat)),
    Tendsto
      (fun n => (plusBoxCurrentMeasure d n beta hbeta.le :
          Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentCylinder S A)) atTop
      (nhds ((infinitePlusCurrentMeasure d beta hbeta.le :
          Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentCylinder S A)))
  free_cylinder : forall (S : Finset (Sym2 (Site d)))
      (A : Set (↑S -> Nat)),
    Tendsto
      (fun n => (freeBoxCurrentMeasure d n beta hbeta.le :
          Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentCylinder S A)) atTop
      (nhds ((infiniteFreeCurrentMeasure d beta hbeta.le :
          Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentCylinder S A)))
  mixed_switching : forall (N : Nat) (x y : Site d)
      (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y)
      (Q : Set (ConfigSpace (Sym2 (Site d)))), IsClopen Q ->
    ((∫ omega, spinProd ({x, y} : Finset (Site d)) omega
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) *
      (∫ omega, spinProd ({x, y} : Finset (Site d)) omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) *
      (((infinitePlusPairSourceCurrentMeasure
          d N beta hbeta x y hx hy hxy).prod
        (infiniteFreePairSourceCurrentMeasure
          d N beta hbeta x y hx hy hxy) : Measure _).real
            (superposedCurrentTrace ⁻¹' Q)) =
      (((infinitePlusCurrentMeasure d beta hbeta.le).prod
        (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _).real
          (currentPairTraceConnectionGate Q x y))


end StatMech.FrontierB
