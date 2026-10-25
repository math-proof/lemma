/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerClose2.Part4
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyClose.Part3
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


section Weighted

variable [Fintype α]


noncomputable def wdpairs (w : α → Bool → ℝ) (𝒜 ℬ : Finset (Finset α)) : ℝ :=
  ∑ p ∈ (𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2), fwt w p.1 * fwt w p.2


noncomputable def wdpairs' (w : α → Bool → ℝ) (i : α) (𝒜 ℬ : Finset (Finset α)) : ℝ :=
  ∑ p ∈ (𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2), fwt' w i p.1 * fwt' w i p.2


noncomputable def fmarg (w : α → Bool → ℝ) (𝒜 : Finset (Finset α)) : ℝ :=
  ∑ S ∈ 𝒜, fwt w S


noncomputable def fmarg' (w : α → Bool → ℝ) (i : α) (𝒜 : Finset (Finset α)) : ℝ :=
  ∑ S ∈ 𝒜, fwt' w i S


end Weighted
end StatMech
