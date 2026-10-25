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
import Abbrev.StatisticalMechanics.Code.FrontierA.LeeYangAsano
open scoped ComplexConjugate


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

def leeYangAnchor (v : V) : LeeYangVar G := Sum.inl v

def leeYangHalf (v : V) (e : ↑G.edgeFinset) : LeeYangVar G := Sum.inr (v, e)

noncomputable def leeYangNormalizedEdgeFactor (beta : ℝ)
    (e : ↑G.edgeFinset) (z : LeeYangVar G → ℂ) : ℂ :=
  Sym2.lift ⟨fun u v ↦
    1 + z (leeYangHalf G u e) * z (leeYangHalf G v e) +
      (Real.exp (-2 * beta) : ℂ) *
        (z (leeYangHalf G u e) + z (leeYangHalf G v e)), by
          intro u v
          ring⟩ e.1

noncomputable def leeYangHalfEdgeProduct (beta : ℝ)
    (z : LeeYangVar G → ℂ) : ℂ :=
  (∏ v : V, (1 + z (leeYangAnchor G v))) *
    ∏ e : ↑G.edgeFinset, leeYangNormalizedEdgeFactor G beta e z

noncomputable def leeYangAnchorProduct (z : LeeYangVar G → ℂ) : ℂ :=
  ∏ v : V, (1 + z (leeYangAnchor G v))

noncomputable def leeYangEdgeProduct (beta : ℝ) (z : LeeYangVar G → ℂ) : ℂ :=
  ∏ e : ↑G.edgeFinset, leeYangNormalizedEdgeFactor G beta e z

end StatMech.FrontierA
