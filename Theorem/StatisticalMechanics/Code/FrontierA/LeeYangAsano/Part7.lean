/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.LeeYangPolynomial
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
import Theorem.StatisticalMechanics.Code.FrontierC.LeeYangSymmetry.Part2
import Def.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part6
open scoped ComplexConjugate


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem leeYang_endpoints_mk (e : ↑G.edgeFinset) :
    s(leeYangEndpoint0 G e, leeYangEndpoint1 G e) = e.1 := by
  change Sym2.mk e.1.out.1 e.1.out.2 = e.1
  rw [Sym2.mk, e.1.out_eq]

omit [DecidableEq V] in
theorem leeYang_endpoints_ne (e : ↑G.edgeFinset) :
    leeYangEndpoint0 G e ≠ leeYangEndpoint1 G e := by
  apply SimpleGraph.Adj.ne
  have he : e.1 ∈ G.edgeFinset := e.2
  rw [← leeYang_endpoints_mk G e] at he
  simpa [SimpleGraph.mem_edgeFinset] using he

end StatMech.FrontierA
