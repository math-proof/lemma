/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/SpaceCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Data.Fin.Basic

open InnerProductSpace Submodule Set

namespace SpaceCurves

def IsFrenetCurve {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ContDiff ℝ ⊤ c ∧
  ∀ t, LinearIndependent ℝ (fun i : Fin (n - 1) =>
    iteratedDeriv (i.val + 1) c t)

noncomputable def frenetFrame {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (_hc : IsFrenetCurve c) (t : ℝ) : Fin n → EuclideanSpace ℝ (Fin n) :=
  gramSchmidtOrthonormalBasis finrank_euclideanSpace (fun i : Fin n =>
    if _h : i.val < n - 1 then iteratedDeriv (i.val + 1) c t
    else 0)

noncomputable def frenetCurvature {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (i : Fin (n - 1)) (t : ℝ) : ℝ :=
  @inner ℝ _ _ (frenetFrame c hc t ⟨i.val + 1, by omega⟩)
    (deriv (fun s => frenetFrame c hc s ⟨i.val, by omega⟩) t) /
  ‖deriv c t‖

noncomputable def frenetSerretMatrix {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j : Fin n =>
    if h : j.val = i.val + 1 ∧ i.val < n - 1 then
      -(frenetCurvature c hc ⟨i.val, h.2⟩ t)
    else if h : i.val = j.val + 1 ∧ j.val < n - 1 then
      frenetCurvature c hc ⟨j.val, h.2⟩ t
    else 0)
