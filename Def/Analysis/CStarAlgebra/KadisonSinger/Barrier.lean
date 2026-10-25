/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/Barrier.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Def.Analysis.CStarAlgebra.KadisonSinger.MixedCharPoly
import Lemma.Real.CStarAlgebra.KadisonSinger.MixedCharPoly
import Lemma.Polynomial.RealRooted
import Lemma.Real.CStarAlgebra.KadisonSinger.RealStable
import Lemma.MvPolynomial.PDeriv
import Lemma.Matrix.MvPolynomial
import Def.Algebra.Polynomial.RealRooted.Part2
import Mathlib.Analysis.Matrix.PosDef
import Def.Analysis.CStarAlgebra.KadisonSinger.RealStable
import Mathlib.Topology.Algebra.MvPolynomial
import Def.Algebra.MvPolynomial.PDeriv
import Def.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Lagrange
open scoped BigOperators ComplexOrder Real

open Filter MvPolynomial

/-!
# The Marcus--Spielman--Srivastava barrier bound

This file proves `mixedCharacteristicPolynomial_maxRealRoot_le`: if positive semidefinite
matrices `A i` sum to the identity and each has trace at most `η`, the largest real root of their
mixed characteristic polynomial is at most `(1 + √η) ^ 2`.

The proof is the multivariate barrier argument. For a real-stable polynomial `p` and a point `x`
above its roots, the barrier in direction `i` is `∂ᵢp(x) / p(x)`. Restricted to a line in
direction `j`, `p` becomes a real-rooted polynomial `f` and `∂ᵢp` a polynomial `g` with
`Im (g z / f z) ≤ 0` on the upper half-plane. A Pick-function argument writes `g / f` as a
constant plus simple fractions with positive residues, so each barrier is nonincreasing and convex
along every coordinate direction. Hence, when the `i`-th barrier is at most `1 - 1 / δ`, applying
`1 - ∂ᵢ` and shifting `x` by `δ` in direction `i` keeps the point above the roots without raising
any barrier. Iterating over all coordinates and evaluating the mixed determinant polynomial at
scalar points gives the bound.
-/


namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger
namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

def ksAboveRoots {σ : Type*} (p : MvPolynomial σ ℂ) (x : σ → ℝ) : Prop :=
  ∀ y : σ → ℝ, (∀ i, x i ≤ y i) → 0 < (eval (fun i ↦ (y i : ℂ)) p).re

noncomputable def ksBarrierValue {σ : Type*}
    (p : MvPolynomial σ ℂ) (x : σ → ℝ) (i : σ) : ℝ :=
  (eval (fun j ↦ (x j : ℂ)) (pderiv i p)).re /
    (eval (fun j ↦ (x j : ℂ)) p).re

noncomputable def ksBarrierSlope {σ : Type*}
    (p : MvPolynomial σ ℂ) (x : σ → ℝ) (i j : σ) : ℝ :=
  let a := (eval (fun k ↦ (x k : ℂ)) p).re
  let b := (eval (fun k ↦ (x k : ℂ)) (pderiv i p)).re
  let c := (eval (fun k ↦ (x k : ℂ)) (pderiv j p)).re
  let e := (eval (fun k ↦ (x k : ℂ)) (pderiv j (pderiv i p))).re
  (e * a - b * c) / a ^ 2

def ksShift {σ : Type*} [DecidableEq σ]
    (x : σ → ℝ) (i : σ) (t : ℝ) : σ → ℝ :=
  Function.update x i (x i + t)

def ksShiftList {σ : Type*} [DecidableEq σ]
    (indices : List σ) (x : σ → ℝ) (δ : ℝ) : σ → ℝ :=
  indices.foldl (fun y i ↦ ksShift y i δ) x

def ksMatrixOffset {m : ℕ} (c : ℂ) : Unit ⊕ Fin m → ℂ :=
  Sum.elim (fun _ ↦ 0) (fun _ ↦ c)

def ksScalarOffset {m : ℕ} (c : ℂ) : Unit ⊕ Fin m → ℂ :=
  Sum.elim (fun _ ↦ c) (fun _ ↦ 0)

def ksScalarPoint {m : ℕ} (t : ℝ) : Unit ⊕ Fin m → ℝ :=
  Sum.elim (fun _ ↦ t) (fun _ ↦ 0)

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger
