/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/ArrowImpossibility.lean -/

import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Push

namespace MetaMathlibExt

section

private def Dom {Alt Voter : Type} (electorate : Finset Voter)
    (P : Voter → Alt → Alt → Prop) : Prop :=
  ∀ v ∈ electorate, IsPreorder Alt (P v) ∧ ∀ x y : Alt, P v x y ∨ P v y x

private def StrongDec {Alt Voter : Type} (electorate : Finset Voter)
    (F : (Voter → Alt → Alt → Prop) → (Alt → Alt → Prop))
    (G : Finset Voter) (p q : Alt) : Prop :=
  ∀ P : Voter → Alt → Alt → Prop, Dom electorate P →
    (∀ v ∈ G, P v p q ∧ ¬ P v q p) → F P p q ∧ ¬ F P q p

private def WeakDec {Alt Voter : Type} (electorate : Finset Voter)
    (F : (Voter → Alt → Alt → Prop) → (Alt → Alt → Prop))
    (G : Finset Voter) (p q : Alt) : Prop :=
  ∀ P : Voter → Alt → Alt → Prop, Dom electorate P →
    (∀ v ∈ G, P v p q ∧ ¬ P v q p) →
    (∀ v ∈ electorate, v ∉ G → P v q p ∧ ¬ P v p q) →
    F P p q ∧ ¬ F P q p
end
end MetaMathlibExt
