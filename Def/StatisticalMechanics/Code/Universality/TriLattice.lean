/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.SAW
import Abbrev.StatisticalMechanics.Code.Universality.TriLattice


namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


def triStepVec (s : TriStep) : TriSite :=
  fun j =>
    match s, j with
    | 0, 0 => 1  | 0, 1 => 0
    | 1, 0 => -1 | 1, 1 => 0
    | 2, 0 => 0  | 2, 1 => 1
    | 3, 0 => 0  | 3, 1 => -1
    | 4, 0 => 1  | 4, 1 => -1
    | 5, 0 => -1 | 5, 1 => 1


def triReverse (s : TriStep) : TriStep :=
  match s with
  | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4


def triStepN {n : ℕ} (w : Fin n → TriStep) (i : ℕ) : TriSite :=
  if h : i < n then triStepVec (w ⟨i, h⟩) else 0


def triPos {n : ℕ} (w : Fin n → TriStep) (k : ℕ) : TriSite :=
  ∑ i ∈ Finset.range k, triStepN w i


def TriIsSAW {n : ℕ} (w : Fin n → TriStep) : Prop :=
  ∀ k1 k2 : ℕ, k1 ≤ n → k2 ≤ n → triPos w k1 = triPos w k2 → k1 = k2


def TriIsNB {n : ℕ} (w : Fin n → TriStep) : Prop :=
  ∀ i : Fin n, ∀ (h : (i : ℕ) + 1 < n), w ⟨(i : ℕ) + 1, h⟩ ≠ triReverse (w i)


noncomputable def triSAWWalks (n : ℕ) : Finset (Fin n → TriStep) :=
  Finset.univ.filter (fun w => TriIsSAW w)


noncomputable def triNBWalks (n : ℕ) : Finset (Fin n → TriStep) :=
  Finset.univ.filter (fun w => TriIsNB w)


noncomputable def triSAWCount (n : ℕ) : ℕ := (triSAWWalks n).card


noncomputable def triNBCount (n : ℕ) : ℕ := (triNBWalks n).card

end StatMech.Universality
