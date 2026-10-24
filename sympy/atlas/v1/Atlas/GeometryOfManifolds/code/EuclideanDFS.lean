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
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.DifferentialForms
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms

noncomputable section

/-- Shorthand for $n$-dimensional Euclidean space $\mathbb{R}^n$ with its standard inner product. -/
abbrev Eℝ (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The space $\Omega^p(\mathbb{R}^n)$ of (not-necessarily-smooth) differential $p$-forms on
$\mathbb{R}^n$: pointwise alternating $\mathbb{R}$-multilinear maps
$(\mathbb{R}^n)^p \to \mathbb{R}$. -/
def EuclideanΩ (n : ℕ) (p : ℕ) :=
  Eℝ n → (Eℝ n [⋀^Fin p]→ₗ[ℝ] ℝ)

/-- The space of vector fields $\mathfrak{X}(\mathbb{R}^n)$ on Euclidean space: arbitrary maps
$\mathbb{R}^n \to \mathbb{R}^n$. -/
def EuclideanVF (n : ℕ) :=
  Eℝ n → Eℝ n

namespace EuclideanΩ

variable {n p : ℕ}

/-- Pointwise abelian-group structure on $\Omega^p(\mathbb{R}^n)$. -/
instance instAddCommGroup : AddCommGroup (EuclideanΩ n p) := Pi.addCommGroup

/-- Pointwise $\mathbb{R}$-module structure on $\Omega^p(\mathbb{R}^n)$. -/
instance instModule : Module ℝ (EuclideanΩ n p) := Pi.module _ _ _

/-- Extensionality for Euclidean $p$-forms: two forms agreeing pointwise are equal. -/
@[ext]
theorem ext {α β : EuclideanΩ n p} (h : ∀ x, α x = β x) : α = β :=
  funext h

/-- Continuous-fibre version of `EuclideanΩ`: pointwise *continuous* alternating multilinear maps.
This is the regularity needed for the differential to be defined via `fderiv`. -/
abbrev CEuclideanΩ (n : ℕ) (p : ℕ) := Eℝ n → (Eℝ n [⋀^Fin p]→L[ℝ] ℝ)

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

section ContinuousLift

/-- Every alternating multilinear form $f : (\mathbb{R}^n)^p \to \mathbb{R}$ is automatically
continuous, since on the finite-dimensional Euclidean space $\mathbb{R}^n$ it is a finite
polynomial in the coordinates of its arguments. -/
lemma AlternatingMap.continuous_of_euclidean {n p : ℕ}
    (f : Eℝ n [⋀^Fin p]→ₗ[ℝ] ℝ) : Continuous (⇑f : (Fin p → Eℝ n) → ℝ) := by

  have key : ∀ m : Fin p → Eℝ n,
      f m = ∑ r : Fin p → Fin n,
        (∏ i : Fin p, (m i (r i) : ℝ)) *
          f (fun i => EuclideanSpace.single (r i) (1 : ℝ)) := by
    intro m
    have hdecomp : m = fun i => ∑ j : Fin n, m i j • EuclideanSpace.single j (1 : ℝ) := by
      ext i k; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hdecomp]

    change f.toMultilinearMap _ = _
    rw [f.toMultilinearMap.map_sum]
    congr 1; ext r

    change f.toMultilinearMap _ = _
    rw [show (fun i => m i (r i) • EuclideanSpace.single (r i) (1 : ℝ)) =
      (fun i => (m i (r i) : ℝ) • (fun i => EuclideanSpace.single (r i) (1 : ℝ)) i) from rfl]
    rw [f.toMultilinearMap.map_smul_univ]
    simp [smul_eq_mul]

  rw [show ⇑f = (fun m => ∑ r : Fin p → Fin n,
      (∏ i : Fin p, (m i (r i) : ℝ)) *
        f (fun i => EuclideanSpace.single (r i) (1 : ℝ))) from funext key]
  apply continuous_finset_sum _ (fun r _ => ?_)
  apply Continuous.mul
  · apply continuous_finset_prod _ (fun i _ => ?_)
    exact ((EuclideanSpace.proj (r i)).continuous).comp (continuous_apply i)
  · exact continuous_const

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
