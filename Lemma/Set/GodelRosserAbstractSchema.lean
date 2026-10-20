import Mathlib
import sympy.Basic
import sympy.atlas.Logic.GodelRosserAbstractSchema
open MetaMathlibExt


/--
[godel_rosser_abstract_schema](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Logic/GodelRosserAbstractSchema.lean)
-/
@[path]
private lemma godel_rosser_abstract_schema_eq
  :
-- imply
  ∀ (Sentence : Type)
    (neg : Sentence → Sentence) (imp : Sentence → Sentence → Sentence)
    (subst : Sentence → ℕ → Sentence)
    (Provable RProvable TrueInN : Sentence → Prop)
    (Proof : Sentence → ℕ → Prop) (rPr : Sentence) (code : Sentence → ℕ),
    (∀ G, TrueInN (neg G) ↔ ¬ TrueInN G) →
    (∀ A B, Provable (imp A B) → Provable A → Provable B) →
    (∀ A, Provable A → Provable (neg A) → False) →
    (∀ A n, subst (neg A) n = neg (subst A n)) →
    (∀ s, Provable s ↔ ∃ n, Proof s n) →
    (∀ s, RProvable s ↔ ∃ n, Proof s n ∧ ∀ m, m < n → ¬ Proof (neg s) m) →
    (∀ s, TrueInN (subst rPr (code s)) ↔ RProvable s) →
    (∀ s, RProvable s → Provable (subst rPr (code s))) →
    (∀ s, Provable (neg s) → Provable (neg (subst rPr (code s)))) →
    (∀ F, ∃ G, (∀ n, subst G n = G) ∧
    Provable (imp G (subst F (code G))) ∧
    Provable (imp (subst F (code G)) G) ∧
    (TrueInN G ↔ TrueInN (subst F (code G)))) →
    ∃ G : Sentence, (∀ n, subst G n = G) ∧
    TrueInN G ∧ ¬ Provable G ∧ ¬ Provable (neg G) := by
-- proof
  apply MetaMathlibExt.godel_rosser_abstract_schema


-- created on 2026-10-20
