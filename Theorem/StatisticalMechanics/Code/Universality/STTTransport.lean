/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.STT.Part4
open SimpleGraph


namespace StatMech

namespace Universality

variable {V : Type*}


theorem bypass_vertex (G1 G2 : SimpleGraph V) (O : V)
    (hedge : ∀ a b, a ≠ O → b ≠ O → G1.Adj a b → G2.Reachable a b)
    (hcorner : ∀ s t, s ≠ O → t ≠ O → G1.Adj s O → G1.Adj O t → G2.Reachable s t)
    {u v : V} (hu : u ≠ O) (hv : v ≠ O) (h : G1.Reachable u v) : G2.Reachable u v := by
  obtain ⟨w⟩ := h
  induction n : w.length using Nat.strong_induction_on generalizing u v with
  | _ n IH =>
    subst n
    match w with
    | .nil => exact Reachable.refl _
    | .cons (v := b) hab w' =>
      by_cases hb : b = O
      · match w' with
        | .nil => exact absurd hb hv
        | .cons (v := c) hbc w'' =>
          have hc : c ≠ O := by intro hcO; subst hcO; exact (G1.ne_of_adj hbc) hb
          have hbO : G1.Adj u O := hb ▸ hab
          have hOc : G1.Adj O c := hb ▸ hbc
          exact (hcorner u c hu hc hbO hOc).trans
            (IH w''.length (by simp only [SimpleGraph.Walk.length_cons]; omega) hc hv w'' rfl)
      · exact (hedge u b hu hb hab).trans
          (IH w'.length (by simp only [SimpleGraph.Walk.length_cons]; omega) hb hv w' rfl)


theorem reach_collapse (G1 G2 : SimpleGraph V) (ρ : V → V)
    (hcell : ∀ a b, G1.Adj a b → G2.Reachable (ρ a) (ρ b))
    {u v : V} (hu : ρ u = u) (hv : ρ v = v) (h : G1.Reachable u v) : G2.Reachable u v := by
  obtain ⟨w⟩ := h
  have key : ∀ {x y : V}, (G1.Walk x y) → G2.Reachable (ρ x) (ρ y) := by
    intro x y w
    induction w with
    | nil => exact Reachable.refl _
    | @cons a b c hab w ih => exact (hcell a b hab).trans ih
  have := key w
  rwa [hu, hv] at this


end Universality
end StatMech
