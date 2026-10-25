/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part8
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace AlignedCrossNestedPairedSequence

noncomputable def transitionA0
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (_data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding) (_n : Nat) : Real := 0

noncomputable def transitionB0
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding) (n : Nat) : Real :=
  (data.triple n).currentX

noncomputable def transitionC0
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (_data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding) (_n : Nat) : Real :=
  -(padding : Real)

noncomputable def transitionD0
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding) (n : Nat) : Real :=
  (data.triple n).currentY + padding

noncomputable def transitionA1
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding) (n : Nat) : Real :=
  (data.triple n).current.raw.data.wideLeft - padding

noncomputable def transitionB1
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding) (n : Nat) : Real :=
  (data.triple n).current.raw.data.wideRight + padding

noncomputable def transitionC1
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (_data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding) (_n : Nat) : Real := 0

noncomputable def transitionD1
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding) (n : Nat) : Real :=
  (data.triple n).currentY


end AlignedCrossNestedPairedSequence
end StatMech.FK.PeriodicPlanar
