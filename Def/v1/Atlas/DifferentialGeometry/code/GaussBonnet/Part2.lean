/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussBonnet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.LinearCombination
import Def.v1.Atlas.DifferentialGeometry.code.GaussMapDegree.Part4
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.GaussMapDegree
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.Hypersurfaces
import Def.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
import Structure.v1.Atlas.DifferentialGeometry.code.GaussBonnet.Part2
open Finset Real


namespace CombinatorialGaussBonnet

attribute [instance] CompactCombinatorialSurface.finVertex

attribute [instance] CompactCombinatorialSurface.finEdge

attribute [instance] CompactCombinatorialSurface.decEdge

variable (S : CompactCombinatorialSurface)

attribute [instance] SurfaceTriangulation.finV

attribute [instance] SurfaceTriangulation.finE

attribute [instance] SurfaceTriangulation.finF

attribute [instance] SurfaceTriangulation.decV

attribute [instance] SurfaceTriangulation.decF

variable (T : SurfaceTriangulation)

noncomputable def SurfaceTriangulation.numVertices : ℕ := Fintype.card T.V

noncomputable def SurfaceTriangulation.numEdges : ℕ := Fintype.card T.E

noncomputable def SurfaceTriangulation.numFaces : ℕ := Fintype.card T.F

noncomputable def SurfaceTriangulation.eulerCharacteristic : ℤ :=
  (T.numVertices : ℤ) - (T.numEdges : ℤ) + (T.numFaces : ℤ)

noncomputable def SurfaceTriangulation.gaussCurvatureComb (v : T.V) : ℝ :=
  2 * π - (T.facesAt v).sum (T.angleAt v)

end CombinatorialGaussBonnet
