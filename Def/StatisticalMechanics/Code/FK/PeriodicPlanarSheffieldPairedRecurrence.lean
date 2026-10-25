/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace PairedMixedBoundaryScores

noncomputable def primalBottomSource
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    Finset V :=
  S.image (P.shift (data.base + preferenceGridSite
    ((0 : Fin (data.width + 1)), (0 : Fin (data.height + 1)))))

noncomputable def primalTopSource
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    Finset V :=
  S.image (P.shift (data.base + preferenceGridSite
    ((0 : Fin (data.width + 1)), Fin.last data.height)))

noncomputable def primalLeftSource
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    Finset V :=
  S.image (P.shift (data.base + preferenceGridSite
    ((0 : Fin (data.width + 1)), (0 : Fin (data.height + 1)))))

noncomputable def primalRightSource
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    Finset V :=
  S.image (P.shift (data.base + preferenceGridSite
    (Fin.last data.width, (0 : Fin (data.height + 1)))))

noncomputable def dualBottomSource
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    Finset W :=
  Sdual.image (Pdual.shift (data.baseDual + preferenceGridSite
    ((0 : Fin (data.widthDual + 1)), (0 : Fin (data.heightDual + 1)))))

noncomputable def dualTopSource
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    Finset W :=
  Sdual.image (Pdual.shift (data.baseDual + preferenceGridSite
    ((0 : Fin (data.widthDual + 1)), Fin.last data.heightDual)))

noncomputable def dualLeftSource
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    Finset W :=
  Sdual.image (Pdual.shift (data.baseDual + preferenceGridSite
    ((0 : Fin (data.widthDual + 1)), (0 : Fin (data.heightDual + 1)))))

noncomputable def dualRightSource
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) :
    Finset W :=
  Sdual.image (Pdual.shift (data.baseDual + preferenceGridSite
    (Fin.last data.widthDual, (0 : Fin (data.heightDual + 1)))))

end PairedMixedBoundaryScores
end StatMech.FK.PeriodicPlanar
