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
import Def.StatisticalMechanics.Code.Sharpness.CToOne.Part2
open scoped BigOperators
open Filter Topology


namespace StatMech

namespace Sharpness

open Ising

open Lattice


variable {V : Type*} [Fintype V] [DecidableEq V]


variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem sct_cInfDep_le_one (ι : ℕ → Type*) [∀ n, DecidableEq (ι n)]
    (M : ℕ → ℝ) (sites : (n : ℕ) → Finset (ι n))
    (m : (n : ℕ) → ι n → ℝ) (hne : ∀ n, (sites n).Nonempty)
    (o : (n : ℕ) → ι n) (ho : ∀ n, o n ∈ sites n)
    (hoM : ∀ n, m n (o n) = M n) (hMne : ∀ n, M n ≠ 0) (n : ℕ) :
    sct_cInfDep ι M sites m hne n ≤ 1 := by
  unfold sct_cInfDep
  calc
    (sites n).inf' (hne n) (fun y => M n / m n y) ≤ M n / m n (o n) :=
      Finset.inf'_le _ (ho n)
    _ = 1 := by rw [hoM n]; exact div_self (hMne n)


theorem sct_ratio_le_cInfDep (ι : ℕ → Type*) [∀ n, DecidableEq (ι n)]
    (M : ℕ → ℝ) (sites : (n : ℕ) → Finset (ι n))
    (m : (n : ℕ) → ι n → ℝ) (hne : ∀ n, (sites n).Nonempty)
    (hmpos : ∀ n y, y ∈ sites n → 0 < m n y) (hMnn : ∀ n, 0 ≤ M n)
    (hbox : ∀ n y, y ∈ sites n → m n y ≤ M (2 * n)) (n : ℕ) :
    M n / M (2 * n) ≤ sct_cInfDep ι M sites m hne n := by
  unfold sct_cInfDep
  refine Finset.le_inf' (hne n) _ ?_
  intro y hy
  exact sct_ratio_lower (hmpos n y hy) (hbox n y hy) (hMnn n)


theorem sct_cInfDep_to_one (ι : ℕ → Type*) [∀ n, DecidableEq (ι n)]
    (M : ℕ → ℝ) (sites : (n : ℕ) → Finset (ι n))
    (m : (n : ℕ) → ι n → ℝ) (hne : ∀ n, (sites n).Nonempty)
    {L : ℝ} (hLpos : 0 < L) (hM : Tendsto M atTop (𝓝 L))
    (hmpos : ∀ n y, y ∈ sites n → 0 < m n y) (hMnn : ∀ n, 0 ≤ M n)
    (hMne : ∀ n, M n ≠ 0) (o : (n : ℕ) → ι n)
    (ho : ∀ n, o n ∈ sites n) (hoM : ∀ n, m n (o n) = M n)
    (hbox : ∀ n y, y ∈ sites n → m n y ≤ M (2 * n)) :
    Tendsto (sct_cInfDep ι M sites m hne) atTop (𝓝 1) :=
  sct_c_to_one M (sct_cInfDep ι M sites m hne) hLpos hM
    (sct_ratio_le_cInfDep ι M sites m hne hmpos hMnn hbox)
    (sct_cInfDep_le_one ι M sites m hne o ho hoM hMne)


theorem sct_cInfDep_to_one_of_monotone (ι : ℕ → Type*) [∀ n, DecidableEq (ι n)]
    (M : ℕ → ℝ) (sites : (n : ℕ) → Finset (ι n))
    (m : (n : ℕ) → ι n → ℝ) (hne : ∀ n, (sites n).Nonempty)
    (hmono : Monotone M) (hub : ∀ n, M n ≤ 1) (hM0 : 0 < M 0)
    (hmpos : ∀ n y, y ∈ sites n → 0 < m n y)
    (o : (n : ℕ) → ι n) (ho : ∀ n, o n ∈ sites n)
    (hoM : ∀ n, m n (o n) = M n)
    (hbox : ∀ n y, y ∈ sites n → m n y ≤ M (2 * n)) :
    Tendsto (sct_cInfDep ι M sites m hne) atTop (𝓝 1) := by
  let L : ℝ := ⨆ n, M n
  have hbdd : BddAbove (Set.range M) := ⟨1, by rintro _ ⟨n, rfl⟩; exact hub n⟩
  have hM : Tendsto M atTop (𝓝 L) := tendsto_atTop_ciSup hmono hbdd
  have h0L : M 0 ≤ L := by
    exact le_ciSup hbdd 0
  have hLpos : 0 < L := lt_of_lt_of_le hM0 h0L
  have hMpos : ∀ n, 0 < M n := by
    intro n
    exact lt_of_lt_of_le hM0 (hmono (Nat.zero_le n))
  exact sct_cInfDep_to_one ι M sites m hne hLpos hM hmpos
    (fun n => (hMpos n).le) (fun n => (hMpos n).ne') o ho hoM hbox

end Sharpness
end StatMech
