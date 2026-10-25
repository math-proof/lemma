/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOne.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.GHSFull.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Def.StatisticalMechanics.Code.Sharpness.CToOne
open scoped BigOperators
open Filter Topology


namespace StatMech

namespace Sharpness

open Ising

open Lattice


variable {V : Type*} [Fintype V] [DecidableEq V]


variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem sct_cInf_le_one (M : ℕ → ℝ) (sites : ℕ → Finset ℕ) (m : ℕ → ℕ → ℝ)
    (hne : ∀ n, (sites n).Nonempty) (o : ℕ → ℕ) (ho : ∀ n, o n ∈ sites n)
    (hoM : ∀ n, m n (o n) = M n) (hMne : ∀ n, M n ≠ 0) (n : ℕ) :
    sct_cInf M sites m hne n ≤ 1 := by
  unfold sct_cInf
  calc (sites n).inf' (hne n) (fun y => M n / m n y)
      ≤ M n / m n (o n) := Finset.inf'_le _ (ho n)
    _ = 1 := by rw [hoM n]; exact div_self (hMne n)


theorem sct_ratio_le_cInf (M : ℕ → ℝ) (sites : ℕ → Finset ℕ) (m : ℕ → ℕ → ℝ)
    (hne : ∀ n, (sites n).Nonempty)
    (hmpos : ∀ n y, y ∈ sites n → 0 < m n y) (hMnn : ∀ n, 0 ≤ M n)
    (hbox : ∀ n y, y ∈ sites n → m n y ≤ M (2 * n)) (n : ℕ) :
    M n / M (2 * n) ≤ sct_cInf M sites m hne n := by
  unfold sct_cInf
  refine Finset.le_inf' (hne n) _ ?_
  intro y hy
  exact sct_ratio_lower (hmpos n y hy) (hbox n y hy) (hMnn n)


theorem sct_cInf_to_one (M : ℕ → ℝ) (sites : ℕ → Finset ℕ) (m : ℕ → ℕ → ℝ)
    (hne : ∀ n, (sites n).Nonempty) {L : ℝ} (hLpos : 0 < L)
    (hM : Tendsto M atTop (𝓝 L))
    (hmpos : ∀ n y, y ∈ sites n → 0 < m n y) (hMnn : ∀ n, 0 ≤ M n)
    (hMne : ∀ n, M n ≠ 0)
    (o : ℕ → ℕ) (ho : ∀ n, o n ∈ sites n) (hoM : ∀ n, m n (o n) = M n)
    (hbox : ∀ n y, y ∈ sites n → m n y ≤ M (2 * n)) :
    Tendsto (sct_cInf M sites m hne) atTop (𝓝 1) :=
  sct_c_to_one M (sct_cInf M sites m hne) hLpos hM
    (sct_ratio_le_cInf M sites m hne hmpos hMnn hbox)
    (sct_cInf_le_one M sites m hne o ho hoM hMne)


end Sharpness
end StatMech
