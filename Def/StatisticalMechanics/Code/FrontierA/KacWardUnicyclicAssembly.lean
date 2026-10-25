/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardUnicyclicAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardCycleAssembly.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnicyclicAssembly
open scoped BigOperators


namespace StatMech.FrontierA

open Matrix


noncomputable def kwAcyclicCycleExtension
    {Incoming Core Outgoing : Type*}
    [Fintype Incoming] [DecidableEq Incoming]
    [Fintype Core] [DecidableEq Core]
    [Fintype Outgoing] [DecidableEq Outgoing]
    (incoming : Matrix Incoming Incoming ℂ)
    (incomingToRest : Matrix Incoming (Core ⊕ Outgoing) ℂ)
    (core : Matrix Core Core ℂ)
    (coreToOutgoing : Matrix Core Outgoing ℂ)
    (outgoing : Matrix Outgoing Outgoing ℂ) :
    Matrix (Incoming ⊕ (Core ⊕ Outgoing))
      (Incoming ⊕ (Core ⊕ Outgoing)) ℂ :=
  Matrix.fromBlocks incoming incomingToRest 0
    (Matrix.fromBlocks core coreToOutgoing 0 outgoing)


end StatMech.FrontierA
