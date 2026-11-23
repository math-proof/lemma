/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Data.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Def.v1.Atlas.AnAlgorithmistsToolkit.code.GraphMatrices
public import Theorem.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.GraphMatrices
public import Def.v1.Atlas.AnAlgorithmistsToolkit.code.SingleEdgeLaplacian

@[expose] public section


namespace PSDMatrix

open Matrix

abbrev IsPSD {n : Type*} (M : Matrix n n ℝ) : Prop := M.PosSemidef

abbrev IsPD {n : Type*} (M : Matrix n n ℝ) : Prop := M.PosDef

end PSDMatrix
