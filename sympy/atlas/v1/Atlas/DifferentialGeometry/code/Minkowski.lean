/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Minkowski.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

noncomputable section

open Finset

namespace Minkowski

variable {n : ℕ}

def minkowskiInner (n : ℕ) (v w : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin n, v (Fin.castSucc i) * w (Fin.castSucc i) -
    v (Fin.last n) * w (Fin.last n)

def IsPositiveDefiniteOn (S : Submodule ℝ (Fin (n + 1) → ℝ)) : Prop :=
  ∀ v : Fin (n + 1) → ℝ, v ∈ S → v ≠ 0 → minkowskiInner n v v > 0

def partials (f : (Fin n → ℝ) → (Fin (n + 1) → ℝ)) (x : Fin n → ℝ) :
    Fin n → Fin (n + 1) → ℝ :=
  fun i => fderiv ℝ f x (Pi.single i 1)

structure SpacelikeHypersurface (n : ℕ) where
  U : Set (Fin n → ℝ)
  hU : IsOpen U
  f : (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  smooth : ContDiffOn ℝ ⊤ f U
  linearIndep : ∀ x ∈ U, LinearIndependent ℝ (partials f x)
  spacelike : ∀ x ∈ U, IsPositiveDefiniteOn
    (Submodule.span ℝ (Set.range (partials f x)))

def orientationMatrix (f : (Fin n → ℝ) → (Fin (n + 1) → ℝ)) (x : Fin n → ℝ)
    (ν : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun (i : Fin (n + 1)) (j : Fin (n + 1)) =>
    Fin.lastCases (ν i) (fun k => partials f x k i) j

structure IsGaussNormal {n : ℕ} (S : SpacelikeHypersurface n) (x : Fin n → ℝ)
    (ν : Fin (n + 1) → ℝ) : Prop where
  timelike : minkowskiInner n ν ν = -1
  orthogonal : ∀ i : Fin n, minkowskiInner n ν (partials S.f x i) = 0
  positive_orientation : (orientationMatrix S.f x ν).det > 0
