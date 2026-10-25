/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/GibbardSatterthwaite.lean -/

import Mathlib.Data.Fintype.Basic
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Lemma.Set.SocialChoice.Arrow
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Push
import Def.GameTheory.SocialChoice.Arrow.Part3


section

namespace MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

/-! # Gibbard–Satterthwaite theorem

Records onto and strategy-proof resolute SCFs over strict total orders.
Reuses the shared strict-order bundle.
-/

/-- Strict total order for strict preference, reused from the shared order module. -/
abbrev StrictTotalOrder (α : Type*) :=
  MathlibExt.Order.StrictTotalOrder α

namespace StrictTotalOrder

/-- Compatibility alias for the former `GibbardSatterthwaiteWanted.StrictTotalOrder.mk`
constructor.

For new code, use `MathlibExt.Order.StrictTotalOrder.mk` directly. -/
abbrev mk {α : Type*} (lt : α → α → Prop)
    (irrefl : ∀ a, ¬lt a a)
    (trans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (total : ∀ {a b}, a ≠ b → lt a b ∨ lt b a) :
    StrictTotalOrder α :=
  MathlibExt.Order.StrictTotalOrder.mk lt irrefl trans total

/-- Compatibility alias for the former `GibbardSatterthwaiteWanted.StrictTotalOrder.lt`
projection.

For new code, use `MathlibExt.Order.StrictTotalOrder.lt` directly. -/
abbrev lt {α : Type*} (self : StrictTotalOrder α) : α → α → Prop :=
  MathlibExt.Order.StrictTotalOrder.lt self

/-- Compatibility alias for the former `GibbardSatterthwaiteWanted.StrictTotalOrder.irrefl`
projection.

For new code, use `MathlibExt.Order.StrictTotalOrder.irrefl` directly. -/
abbrev irrefl {α : Type*} (self : StrictTotalOrder α) (a : α) : ¬self.lt a a :=
  MathlibExt.Order.StrictTotalOrder.irrefl self a

/-- Compatibility alias for the former `GibbardSatterthwaiteWanted.StrictTotalOrder.trans`
projection.

For new code, use `MathlibExt.Order.StrictTotalOrder.trans` directly. -/
abbrev trans {α : Type*} (self : StrictTotalOrder α) {a b c : α}
    (h1 : self.lt a b) (h2 : self.lt b c) : self.lt a c :=
  MathlibExt.Order.StrictTotalOrder.trans self h1 h2

/-- Compatibility alias for the former `GibbardSatterthwaiteWanted.StrictTotalOrder.total`
projection.

For new code, use `MathlibExt.Order.StrictTotalOrder.total` directly. -/
abbrev total {α : Type*} (self : StrictTotalOrder α) {a b : α} (h : a ≠ b) :
    self.lt a b ∨ self.lt b a :=
  MathlibExt.Order.StrictTotalOrder.total self h

end StrictTotalOrder

/-- Profile of strict total orders. -/
abbrev Profile (Alt Voter : Type*) := Voter → StrictTotalOrder Alt

/-- Resolute social choice function: profile ↦ chosen alternative. -/
abbrev SocialChoiceFunction (Alt Voter : Type*) := Profile Alt Voter → Alt

end MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted
end
