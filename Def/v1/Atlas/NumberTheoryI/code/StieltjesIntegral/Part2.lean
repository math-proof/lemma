/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/StieltjesIntegral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Structure.v1.Atlas.NumberTheoryI.code.StieltjesIntegral.Part2


namespace RiemannStieltjes

variable {a b : ℝ}

noncomputable def stieltjesSum {𝕜 : Type*} [NormedField 𝕜]
    (PT : TaggedPartition a b) (f g : ℝ → 𝕜) : 𝕜 :=
  ∑ k : Fin PT.n,
    f (PT.tags k) * (g (PT.pts ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) -
                      g (PT.pts ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩))

def HasStieltjesIntegral {𝕜 : Type*} [NormedField 𝕜]
    (f g : ℝ → 𝕜) (a b : ℝ) (S : 𝕜) : Prop :=
  ∀ ε > 0, ∃ Pε : IntervalPartition a b,
    ∀ (PT : TaggedPartition a b),
      PT.toIntervalPartition.IsRefinementOf Pε →
      ‖stieltjesSum PT f g - S‖ < ε

def StieltjesIntegrable {𝕜 : Type*} [NormedField 𝕜]
    (f g : ℝ → 𝕜) (a b : ℝ) : Prop :=
  ∃ S, HasStieltjesIntegral f g a b S

noncomputable def IntervalPartition.pointSet (P : IntervalPartition a b) : Finset ℝ :=
  Finset.univ.image P.pts

noncomputable def stieltjesIntegral {𝕜 : Type*} [NormedField 𝕜]
    (f g : ℝ → 𝕜) (a b : ℝ) : 𝕜 := by
  classical exact if h : StieltjesIntegrable f g a b then h.choose else 0

def IsBoundedVariation {𝕜 : Type*} [NormedField 𝕜] (f : ℝ → 𝕜) (a b : ℝ) : Prop :=
  ∃ M : ℝ, ∀ P : IntervalPartition a b,
    (∑ k : Fin P.n,
      ‖f (P.pts ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) -
       f (P.pts ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩)‖) < M

noncomputable def cumRefine
    (P : ℕ → IntervalPartition a b)
    (cr : ∀ Q R : IntervalPartition a b,
      ∃ S : IntervalPartition a b, S.IsRefinementOf Q ∧ S.IsRefinementOf R) :
    ℕ → IntervalPartition a b
  | 0 => P 0
  | n + 1 => (cr (cumRefine P cr n) (P (n + 1))).choose

end RiemannStieltjes
