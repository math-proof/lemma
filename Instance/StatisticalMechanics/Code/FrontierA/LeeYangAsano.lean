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
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part2
open scoped ComplexConjugate


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

noncomputable local instance leeYangAsanoPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

end StatMech.FrontierA
