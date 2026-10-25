/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

import Mathlib.Data.Fintype.Card
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Theorem.Combinatorics.Matching.GaleShapley.Part3
/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/


namespace MathlibExt.Combinatorics.Matching.GaleShapley

/-- One proposal step: free man `m0` proposes to `w0`, who keeps the better candidate. -/
noncomputable def dostep {M W : Type*} [DecidableEq M] [DecidableEq W]
    (_mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W) (m0 : M) (w0 : W) :
    DAState M W :=
  { prop := fun m' => if m' = m0 then insert w0 (s.prop m0) else s.prop m',
    hold := fun w' =>
      if w' = w0 then some (womanChoice (wp w0) (s.hold w0) m0) else s.hold w' }

/-- Algorithm invariants: holders exist for proposed-to women; holders were proposed to;
holders are best among proposers; holders are unique; proposals go in preference order. -/
def DAInv {M W : Type*}
    (mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W) : Prop :=
  (∀ w m', w ∈ s.prop m' → ∃ m, s.hold w = some m) ∧
  (∀ w m, s.hold w = some m → w ∈ s.prop m) ∧
  (∀ w m, s.hold w = some m → ∀ m', w ∈ s.prop m' → m' = m ∨ (wp w).lt m m') ∧
  (∀ m w₁ w₂, s.hold w₁ = some m → s.hold w₂ = some m → w₁ = w₂) ∧
  (∀ m w w', w ∈ s.prop m → w' ∉ s.prop m → w ≠ w' → (mp m).lt w w')

end MathlibExt.Combinatorics.Matching.GaleShapley
