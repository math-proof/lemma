/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Topology.Algebra.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Abbrev.v1.Atlas.GeometryOfManifolds.code.EuclideanDFS.Part2


noncomputable section

namespace EuclideanΩ

variable {n p : ℕ}

section ExteriorDerivative

variable {n p : ℕ}

/-- Identify a $0$-form $\alpha : \mathbb{R}^n \to \mathrm{Alt}^0(\mathbb{R}^n;\mathbb{R})$ with
its underlying scalar function $x \mapsto \alpha(x)()$. -/
def zeroFormScalar (α : EuclideanΩ n 0) : Eℝ n → ℝ := fun x => α x Fin.elim0

/-- Exterior derivative of a $0$-form: $d f$ as the $1$-form whose value at $x$ is the linear
map $v \mapsto Df(x)(v)$. -/
def euclideanD0 (α : EuclideanΩ n 0) : EuclideanΩ n 1 :=
  fun x =>
    (AlternatingMap.ofSubsingleton ℝ (Eℝ n) ℝ (0 : Fin 1))
      ((fderiv ℝ (zeroFormScalar α) x).toLinearMap)

/-- Auxiliary helper: the Fréchet derivative $D\alpha(x)$ of a continuous-fibre $p$-form viewed
as a linear map $\mathbb{R}^n \to \mathrm{Alt}^p(\mathbb{R}^n; \mathbb{R})$. -/
def fderivToAltMap (α : CEuclideanΩ n p) (x : Eℝ n) :
    Eℝ n →ₗ[ℝ] (Eℝ n [⋀^Fin p]→ₗ[ℝ] ℝ) :=
  (ContinuousAlternatingMap.toAlternatingMapLinear (R := ℝ) (A := ℝ)).comp
    (fderiv ℝ α x).toLinearMap

/-- Variant of `fderivToAltMap` landing in plain `MultilinearMap`s, used in the explicit
`uncurryMid` construction of $d\alpha$. -/
def fderivToMMap (α : CEuclideanΩ n p) (x : Eℝ n) :
    Eℝ n →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin p => Eℝ n) ℝ :=
  ((AlternatingMap.toMultilinearMapLM (S := ℝ)).comp
    (ContinuousAlternatingMap.toAlternatingMapLinear (R := ℝ) (A := ℝ))).comp
    (fderiv ℝ α x).toLinearMap

/-- Intermediate non-alternated $(p+1)$-multilinear map obtained by uncurrying the derivative
$D\alpha(x)$ in the first slot. -/
def euclideanD_M0 (α : CEuclideanΩ n p) (x : Eℝ n) :
    MultilinearMap ℝ (fun _ : Fin (p + 1) => Eℝ n) ℝ :=
  LinearMap.uncurryMid (0 : Fin (p + 1)) (fderivToMMap α x)

/-- Exterior derivative $d : \Omega^p \to \Omega^{p+1}$ on continuous-fibre forms, defined
pointwise as the antisymmetrisation of the uncurried Fréchet derivative. -/
def euclideanD (α : CEuclideanΩ n p) : EuclideanΩ n (p + 1) :=
  fun x => AlternatingMap.alternatizeUncurryFin (fderivToAltMap α x)

end ExteriorDerivative
end EuclideanΩ
end
