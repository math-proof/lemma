/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverageShells.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
open Finset MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


noncomputable def PeriodicGraph.orbitVertexToBuffered
    (P : PeriodicGraph V) (n : Nat) :
    P.OrbitVertex n ↪ P.BufferedVertex n where
  toFun x := ⟨x.1, P.orbitBox_mono (P.id_le_bufferedRadius n) x.2⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : P.BufferedVertex n => z.1) hxy


noncomputable def PeriodicGraph.orbitShellCandidatePairs
    (P : PeriodicGraph V) (n : Nat) :
    Finset (P.BufferedVertex n × P.BufferedVertex n) :=
  ((Finset.univ : Finset (P.OrbitVertex n)) ×ˢ
      (Finset.univ : Finset (P.OrbitVertex n))).image
    (fun xy => (P.orbitVertexToBuffered n xy.1,
      P.orbitVertexToBuffered n xy.2))


noncomputable def PeriodicGraph.canonicalConnectionShellPairs
    (P : PeriodicGraph V) (n : Nat) :
    Finset (P.BufferedVertex n × P.BufferedVertex n) :=
  (P.orbitShellCandidatePairs n).filter
    (fun xy => n ≤ P.graph.dist xy.1.1 xy.2.1)

end StatMech.FK.PeriodicPlanar
