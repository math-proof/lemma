/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalWiredCorrelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part8
import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokalWiredCorrelation
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


noncomputable def wiredConnToBdryProbQ
    (q : Nat) (p : Real) (x : V) : Real :=
  ∑ omega ∈ Finset.univ.filter
      (fun omega : ConfigSpace (Sym2 V) => ConnToBdry G bdry omega x),
    bcProb G (boundaryCliqueGraph bdry) p (q : Real) omega


noncomputable def esWiredPottsCenteredOnePoint
    (q : Nat) (b : Fin q) (p : Real) (x : V) : Real :=
  (∑ omega : ConfigSpace (Sym2 V), ∑ sigma : V → Fin q,
      esWeightWired G bdry b p sigma omega *
        pottsBoundaryObservable q b (sigma x)) /
    esZWired G bdry q b p

end IsingFK
end StatMech
