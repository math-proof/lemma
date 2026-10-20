import Mathlib
import sympy.Basic
import sympy.atlas.GameTheory.SocialChoice.ArrowImpossibility
open MetaMathlibExt


/--
[arrowImpossibility](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/ArrowImpossibility.lean)
-/
@[path]
private lemma arrowImpossibility_eq
  :
-- imply
  ∀ {Alt Voter : Type}
    (electorate : Finset Voter)
    (F : (Voter → Alt → Alt → Prop) → (Alt → Alt → Prop))
    (hexists : ∃ a b c : Alt, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (hNonempty : ∃ d, d ∈ electorate)
    (hUniv : ∀ P : Voter → Alt → Alt → Prop,
    (∀ v ∈ electorate, IsPreorder Alt (P v) ∧ ∀ x y : Alt, P v x y ∨ P v y x) →
    IsPreorder Alt (F P) ∧ ∀ x y : Alt, F P x y ∨ F P y x)
    (hPareto : ∀ (P : Voter → Alt → Alt → Prop) (a b : Alt),
    (∀ v ∈ electorate, IsPreorder Alt (P v) ∧ ∀ x y : Alt, P v x y ∨ P v y x) →
    (∀ v ∈ electorate, P v a b ∧ ¬ P v b a) → F P a b ∧ ¬ F P b a)
    (hIIA : ∀ (P Q : Voter → Alt → Alt → Prop) (a b : Alt),
    (∀ v ∈ electorate, IsPreorder Alt (P v) ∧ ∀ x y : Alt, P v x y ∨ P v y x) →
    (∀ v ∈ electorate, IsPreorder Alt (Q v) ∧ ∀ x y : Alt, Q v x y ∨ Q v y x) →
    (∀ v ∈ electorate, (P v a b ↔ Q v a b) ∧ (P v b a ↔ Q v b a)) →
    (F P a b ↔ F Q a b) ∧ (F P b a ↔ F Q b a))
    (hNoDict : ∀ d ∈ electorate, ∃ (P : Voter → Alt → Alt → Prop) (a b : Alt),
    (∀ v ∈ electorate, IsPreorder Alt (P v) ∧ ∀ x y : Alt, P v x y ∨ P v y x) ∧
    (P d a b ∧ ¬ P d b a) ∧ ¬ (F P a b ∧ ¬ F P b a)),
    False := by
-- proof
  apply MetaMathlibExt.arrowImpossibility


-- created on 2026-10-20
