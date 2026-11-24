module
public import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeIsingAdapter
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeThinBox.Part3
open scoped BigOperators
open Finset
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThinBox.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

def thinBoxPlaquettePreimage (n : ℕ)
    (delta : Finset (Sym2 (Fin (n + 1)))) :
    Finset (thinBoxPlaquette n) :=
  ((thinBoxDualGraph n).edgeFinset.attach.filter
      (fun e => e.1 ∈ delta)).map (thinBoxDualEdge n).symm.toEmbedding

end
end StatMech.FrontierA
