/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import sympy.atlas.v1.Atlas.AnAlgorithmistsToolkit.code.GraphMatrices
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.GraphMatrices
import sympy.atlas.v1.Atlas.AnAlgorithmistsToolkit.code.SingleEdgeLaplacian

namespace PSDMatrix

open Matrix

abbrev IsPSD {n : Type*} (M : Matrix n n ℝ) : Prop := M.PosSemidef

abbrev IsPD {n : Type*} (M : Matrix n n ℝ) : Prop := M.PosDef
