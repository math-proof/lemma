/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.SAW
import Abbrev.StatisticalMechanics.Code.Universality.ConnectiveBounds


namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


def zdStepVec {d : ℕ} (s : ZdStep d) : ZdSite d :=
  fun j => if j = s.1 then (if s.2 then 1 else -1) else 0


def zdReverse {d : ℕ} (s : ZdStep d) : ZdStep d := (s.1, !s.2)


def zdStepN {d n : ℕ} (w : Fin n → ZdStep d) (i : ℕ) : ZdSite d :=
  if h : i < n then zdStepVec (w ⟨i, h⟩) else 0


def zdPos {d n : ℕ} (w : Fin n → ZdStep d) (k : ℕ) : ZdSite d :=
  ∑ i ∈ Finset.range k, zdStepN w i


def ZdIsSAW {d n : ℕ} (w : Fin n → ZdStep d) : Prop :=
  ∀ k1 k2 : ℕ, k1 ≤ n → k2 ≤ n → zdPos w k1 = zdPos w k2 → k1 = k2


def ZdIsNB {d n : ℕ} (w : Fin n → ZdStep d) : Prop :=
  ∀ i : Fin n, ∀ (h : (i : ℕ) + 1 < n), w ⟨(i : ℕ) + 1, h⟩ ≠ zdReverse (w i)


noncomputable def zdSAWWalks (d n : ℕ) : Finset (Fin n → ZdStep d) :=
  Finset.univ.filter (fun w => ZdIsSAW w)


noncomputable def zdNBWalks (d n : ℕ) : Finset (Fin n → ZdStep d) :=
  Finset.univ.filter (fun w => ZdIsNB w)


noncomputable def zdSAWCount (d n : ℕ) : ℕ := (zdSAWWalks d n).card


noncomputable def zdNBCount (d n : ℕ) : ℕ := (zdNBWalks d n).card

end StatMech.Universality
