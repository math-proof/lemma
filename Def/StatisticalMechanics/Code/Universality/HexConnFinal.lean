/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnFinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConnAssembly
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryUncond.Part2


namespace StatMech.Universality

open Filter Topology

open scoped Topology Real NNReal


noncomputable def hexConnFinalLam {a : ℕ → ℂ} {h0 : ℕ → ℤ}
    (B : ∀ v, HexBoundaryDecomp (hexUncondDomain (a v) (h0 v)) (hexUncondPairing (a v) (h0 v))) :
    ℕ → ℝ := fun v => (B v).lam


noncomputable def hexConnFinalTau {a : ℕ → ℂ} {h0 : ℕ → ℤ}
    (B : ∀ v, HexBoundaryDecomp (hexUncondDomain (a v) (h0 v)) (hexUncondPairing (a v) (h0 v))) :
    ℕ → ℝ := fun v => (B v).taup + (B v).taum


noncomputable def hexConnFinalUps {a : ℕ → ℂ} {h0 : ℕ → ℤ}
    (B : ∀ v, HexBoundaryDecomp (hexUncondDomain (a v) (h0 v)) (hexUncondPairing (a v) (h0 v))) :
    ℕ → ℝ := fun v => (B v).ups


end StatMech.Universality
