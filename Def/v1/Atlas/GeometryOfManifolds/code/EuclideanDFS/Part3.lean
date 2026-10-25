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
import Theorem.v1.Atlas.GeometryOfManifolds.code.EuclideanDFS.Part2


noncomputable section

namespace EuclideanΩ

variable {n p : ℕ}

section ContinuousLift

/-- Lift an algebraic alternating map on $\mathbb{R}^n$ to its continuous counterpart, using the
automatic continuity established above. -/
def toCAlt {n p : ℕ} (f : Eℝ n [⋀^Fin p]→ₗ[ℝ] ℝ) : Eℝ n [⋀^Fin p]→L[ℝ] ℝ where
  toContinuousMultilinearMap :=
    { f.toMultilinearMap with cont := AlternatingMap.continuous_of_euclidean f }
  map_eq_zero_of_eq' := f.map_eq_zero_of_eq'

/-- Forget continuity of an alternating multilinear map. -/
def fromCAlt {n p : ℕ} (g : Eℝ n [⋀^Fin p]→L[ℝ] ℝ) : Eℝ n [⋀^Fin p]→ₗ[ℝ] ℝ :=
  g.toAlternatingMap

/-- Pointwise lift of $\alpha \in \Omega^p(\mathbb{R}^n)$ to a continuous-fibre form. -/
def toCEuclideanΩ {n p : ℕ} (α : EuclideanΩ n p) : CEuclideanΩ n p :=
  fun x => toCAlt (α x)

/-- Pointwise forgetful map from continuous-fibre forms back to algebraic ones. -/
def CEuclideanΩ.toEuclideanΩ' {n p : ℕ} (α : EuclideanΩ.CEuclideanΩ n p) : EuclideanΩ n p :=
  fun x => fromCAlt (α x)

/-- Exterior derivative on $\Omega^p(\mathbb{R}^n)$: lift $\alpha$ to a continuous-fibre form,
take $d$ there, and forget continuity. This is the exterior derivative used by the Euclidean
differential form space instance. -/
def euclideanD_lifted {n p : ℕ} (α : EuclideanΩ n p) : EuclideanΩ n (p + 1) :=
  euclideanD (toCEuclideanΩ α)

end ContinuousLift

end EuclideanΩ

/-- Pointwise multiplication of a $p$-form by a $0$-form (scalar function):
$(f \cdot \alpha)(x) = f(x) \cdot \alpha(x)$. -/
def euclideanFMul {n p : ℕ} (f : EuclideanΩ n 0) (α : EuclideanΩ n p) : EuclideanΩ n p :=
  fun x => (f x Fin.elim0) • (α x)

/-- The constant coordinate $1$-form $dx_i$ on $\mathbb{R}^n$: at every point $x$ it sends
$v \in \mathbb{R}^n$ to its $i$-th component $v_i$. -/
def dx_i {n : ℕ} (i : Fin n) : EuclideanΩ n 1 :=
  fun _ => (AlternatingMap.ofSubsingleton ℝ (Eℝ n) ℝ (0 : Fin 1)) (EuclideanSpace.projₗ i)

/-- Interior product (contraction) $\iota_X \alpha$ of a $(p+1)$-form with a vector field
$X$: at each point $x$, it is the $p$-form $v \mapsto \alpha(x)(X(x), v_1, \ldots, v_p)$. -/
def euclideanIota {n : ℕ} (X : EuclideanVF n) {p : ℕ} (α : EuclideanΩ n (p + 1)) :
    EuclideanΩ n p :=
  fun x => (α x).curryLeft (X x)

/-- Identify a pointwise $1$-form with the underlying linear functional $\mathbb{R}^n \to \mathbb{R}$. -/
def oneFormLinear {n : ℕ} (ω_x : Eℝ n [⋀^Fin 1]→ₗ[ℝ] ℝ) : Eℝ n →ₗ[ℝ] ℝ :=
  (AlternatingMap.ofSubsingleton ℝ (Eℝ n) ℝ (0 : Fin 1)).symm ω_x

/-- Pointwise wedge product $\omega \wedge \alpha$ where $\omega$ is a $1$-form and $\alpha$ is
a $p$-form: antisymmetrise the tensor product $\omega \otimes \alpha$ via the uncurry-and-alternate
construction. -/
def wedgePointwise {n p : ℕ}
    (ω_x : Eℝ n [⋀^Fin 1]→ₗ[ℝ] ℝ) (α_x : Eℝ n [⋀^Fin p]→ₗ[ℝ] ℝ) :
    Eℝ n [⋀^Fin (p + 1)]→ₗ[ℝ] ℝ :=
  AlternatingMap.alternatizeUncurryFin ((oneFormLinear ω_x).smulRight α_x)

/-- Wedge product of a Euclidean $1$-form $\omega$ with a $p$-form $\alpha$, defined pointwise
via `wedgePointwise`. -/
def euclideanWedge1 {n : ℕ} (ω : EuclideanΩ n 1) {p : ℕ}
    (α : EuclideanΩ n p) : EuclideanΩ n (p + 1) :=
  fun x => wedgePointwise (ω x) (α x)

/-- Pointwise scalar-function multiplication on continuous-fibre forms: $(g \cdot \alpha)(x) =
g(x) \cdot \alpha(x)$. -/
def cFMul {n p : ℕ} (g : Eℝ n → ℝ) (α : EuclideanΩ.CEuclideanΩ n p) :
    EuclideanΩ.CEuclideanΩ n p :=
  g • α

/-- Forget the continuity data of a continuous-fibre form to get an algebraic Euclidean form. -/
def CEuclideanΩ.toEΩ {n p : ℕ} (α : EuclideanΩ.CEuclideanΩ n p) : EuclideanΩ n p :=
  fun x => (α x).toAlternatingMap

/-- Exterior derivative of a *raw* scalar function $g : \mathbb{R}^n \to \mathbb{R}$, returning
the $1$-form $dg$ with $dg(x)(v) = Dg(x)(v)$. -/
def euclideanD_scalar {n : ℕ} (g : Eℝ n → ℝ) : EuclideanΩ n 1 :=
  fun x => (AlternatingMap.ofSubsingleton ℝ (Eℝ n) ℝ (0 : Fin 1))
    ((fderiv ℝ g x).toLinearMap)

/-- Interior product $\iota_X$ on continuous-fibre forms (the same construction as
`euclideanIota` but preserving continuity of the fibres). -/
def euclideanIotaC {n : ℕ} (X : EuclideanVF n) {p : ℕ} (α : EuclideanΩ.CEuclideanΩ n (p + 1)) :
    EuclideanΩ.CEuclideanΩ n p :=
  fun x => (α x).curryLeft (X x)

/-- Lie derivative of a $(p+1)$-form along a vector field $X$ via Cartan's magic formula:
$\mathcal{L}_X \alpha = d(\iota_X \alpha) + \iota_X(d\alpha)$. -/
def euclideanL {n : ℕ} (X : EuclideanVF n) {p : ℕ}
    (α : EuclideanΩ.CEuclideanΩ n (p + 1)) : EuclideanΩ n (p + 1) :=
  EuclideanΩ.euclideanD (euclideanIotaC X α) + euclideanIota X (EuclideanΩ.euclideanD α)

/-- Lie derivative on $0$-forms: $\mathcal{L}_X f = Df \cdot X$, the directional derivative of
the scalar function underlying $f$ in the direction $X(x)$. -/
def euclideanL0 {n : ℕ} (X : EuclideanVF n) (f : EuclideanΩ n 0) : EuclideanΩ n 0 :=
  fun x => AlternatingMap.constOfIsEmpty ℝ (Eℝ n) (Fin 0)
    (fderiv ℝ (EuclideanΩ.zeroFormScalar f) x (X x))

end

section DFSInstance

variable {n : ℕ}

open EuclideanΩ

/-- Lie derivative $\mathcal{L}_X : \Omega^p \to \Omega^p$ on Euclidean forms, defined via
Cartan's magic formula. On $0$-forms it reduces to $\iota_X d\alpha$, and on $(p+1)$-forms to
$d(\iota_X\alpha) + \iota_X(d\alpha)$. -/
noncomputable def euclideanLie (X : EuclideanVF n) {p : ℕ}
    (α : EuclideanΩ n p) : EuclideanΩ n p :=
  match p with
  | 0 => euclideanIota X (euclideanD_lifted α)
  | _ + 1 => euclideanD_lifted (euclideanIota X α) + euclideanIota X (euclideanD_lifted α)

end DFSInstance
