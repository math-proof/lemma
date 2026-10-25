/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part2
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

open StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
  (boundary : V -> Prop) [DecidablePred boundary]

section NestedBoundary

variable {Vin Vout : Type*} [DecidableEq Vin] [DecidableEq Vout]
  (Gin : SimpleGraph Vin) (Gout : SimpleGraph Vout)
  (incl : Vin → Vout)
  (bdryIn : Vin → Prop) (bdryOut : Vout → Prop)


noncomputable def finiteWiredEventMass {W : Type*} [Fintype W]
    [DecidableEq W] (K : SimpleGraph W) [DecidableRel K.Adj]
    (bdry : W → Prop) [DecidablePred bdry]
    (p q : Real) (A : Set (ConfigSpace (Sym2 W))) : Real :=
  ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
    wiredFkProb K bdry p q omega

end NestedBoundary
end
end StatMech.FK
