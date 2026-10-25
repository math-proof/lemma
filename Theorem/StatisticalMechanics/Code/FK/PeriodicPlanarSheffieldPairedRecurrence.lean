/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace PairedMixedBoundaryScores

theorem primalBottomScore
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    p < mu.real (E.rectSideConnectionEvent
      data.wideLeft data.wideRight 0 data.shortTop
      (data.primalBottomSource : Set V)
      (E.rectBottomBoundaryVertices
        data.wideLeft data.wideRight 0 data.shortTop)) := by
  simpa [primalBottomSource] using
    data.primal_bottom (0 : Fin (data.width + 1))

theorem primalTopScore
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    p < mu.real (E.rectSideConnectionEvent
      data.wideLeft data.wideRight 0 data.shortTop
      (data.primalTopSource : Set V)
      (E.rectTopBoundaryVertices
        data.wideLeft data.wideRight 0 data.shortTop)) := by
  simpa [primalTopSource] using
    data.primal_top (0 : Fin (data.width + 1))

theorem primalLeftScore
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    p < mu.real (E.rectSideConnectionEvent
      0 data.narrowRight 0 data.tallTop
      (data.primalLeftSource : Set V)
      (E.rectLeftBoundaryVertices 0 data.narrowRight 0 data.tallTop)) := by
  simpa [primalLeftSource] using
    data.primal_left (0 : Fin (data.height + 1))

theorem primalRightScore
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    p < mu.real (E.rectSideConnectionEvent
      0 data.narrowRight 0 data.tallTop
      (data.primalRightSource : Set V)
      (E.rectRightBoundaryVertices 0 data.narrowRight 0 data.tallTop)) := by
  simpa [primalRightSource] using
    data.primal_right (0 : Fin (data.height + 1))

theorem dualBottomScore
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    pDual < muDual.real (Edual.rectSideConnectionEvent
      data.wideLeft data.wideRight 0 data.shortTop
      (data.dualBottomSource : Set W)
      (Edual.rectBottomBoundaryVertices
        data.wideLeft data.wideRight 0 data.shortTop)) := by
  simpa [dualBottomSource] using
    data.dual_bottom (0 : Fin (data.widthDual + 1))

theorem dualTopScore
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    pDual < muDual.real (Edual.rectSideConnectionEvent
      data.wideLeft data.wideRight 0 data.shortTop
      (data.dualTopSource : Set W)
      (Edual.rectTopBoundaryVertices
        data.wideLeft data.wideRight 0 data.shortTop)) := by
  simpa [dualTopSource] using
    data.dual_top (0 : Fin (data.widthDual + 1))

theorem dualLeftScore
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    pDual < muDual.real (Edual.rectSideConnectionEvent
      0 data.narrowRight 0 data.tallTop
      (data.dualLeftSource : Set W)
      (Edual.rectLeftBoundaryVertices 0 data.narrowRight 0 data.tallTop)) := by
  simpa [dualLeftSource] using
    data.dual_left (0 : Fin (data.heightDual + 1))

theorem dualRightScore
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    pDual < muDual.real (Edual.rectSideConnectionEvent
      0 data.narrowRight 0 data.tallTop
      (data.dualRightSource : Set W)
      (Edual.rectRightBoundaryVertices 0 data.narrowRight 0 data.tallTop)) := by
  simpa [dualRightSource] using
    data.dual_right (0 : Fin (data.heightDual + 1))

end PairedMixedBoundaryScores
end StatMech.FK.PeriodicPlanar
