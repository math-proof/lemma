/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MengerSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.SimpleGraph.Paths
import Theorem.StatisticalMechanics.Code.Probability.MengerSplice


namespace StatMech.Combinatorics

open SimpleGraph SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V}


def mgs_spliced {ι : Type*} {srcA tgtA wB : ι → V}
    (pA : (i : ι) → G.Walk (srcA i) (tgtA i))
    (pB : (i : ι) → G.Walk (tgtA i) (wB i)) (i : ι) :
    G.Walk (srcA i) (wB i) :=
  (pA i).append (pB i)


end StatMech.Combinatorics
