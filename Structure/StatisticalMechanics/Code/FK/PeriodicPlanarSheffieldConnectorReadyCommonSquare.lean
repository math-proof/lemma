/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldConnectorReadyCommonSquare.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldExclusion
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldConnectorReadyCommonSquare
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


structure PeriodicPlaneEmbedding.ConnectorReadyCommonSquareData
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) (radius : Nat -> Nat) where
  M : Nat -> Nat
  baseLeft : Nat -> Site 2
  baseRight : Nat -> Site 2
  baseBottom : Nat -> Site 2
  baseTop : Nat -> Site 2
  connectorLeft : forall n,
    P.shift (baseLeft n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
      E.rectVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
  connectorRight : forall n,
    P.shift (baseRight n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
      E.rectVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
  connectorBottom : forall n,
    P.shift (baseBottom n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
      E.rectVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
  connectorTop : forall n,
    P.shift (baseTop n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
      E.rectVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
  leftLimit : Tendsto (fun n => mu.real
    (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
      (-(M n : Real)) (M n : Real)
      (P.shift (baseLeft n) '' (P.orbitBox n : Set V))
      (E.rectLeftBoundaryVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)))) atTop (nhds 1)
  rightLimit : Tendsto (fun n => mu.real
    (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
      (-(M n : Real)) (M n : Real)
      (P.shift (baseRight n) '' (P.orbitBox n : Set V))
      (E.rectRightBoundaryVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)))) atTop (nhds 1)
  bottomLimit : Tendsto (fun n => mu.real
    (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
      (-(M n : Real)) (M n : Real)
      (P.shift (baseBottom n) '' (P.orbitBox n : Set V))
      (E.rectBottomBoundaryVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)))) atTop (nhds 1)
  topLimit : Tendsto (fun n => mu.real
    (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
      (-(M n : Real)) (M n : Real)
      (P.shift (baseTop n) '' (P.orbitBox n : Set V))
      (E.rectTopBoundaryVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)))) atTop (nhds 1)


end StatMech.FK.PeriodicPlanar
