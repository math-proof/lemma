module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HilbertSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.MeasureTheory.Function.L2Space


public section

noncomputable section

open scoped ComplexInnerProductSpace

namespace HilbertSpace

/-- A Hilbert space is a complex inner product space that is complete with respect to the norm
induced by the inner product. This is Definition 5.1 of Melrose, packaged as a type class
combining `InnerProductSpace ℂ V` with `CompleteSpace V`. -/
class IsHilbertSpace (V : Type*) [NormedAddCommGroup V] extends
    InnerProductSpace ℂ V, CompleteSpace V

end HilbertSpace
end
