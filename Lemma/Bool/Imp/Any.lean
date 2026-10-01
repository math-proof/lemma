import Lemma.Bool.Imp.Any.of.Imp
import Lemma.Bool.Imp.of.Imp.Any
open Bool


@[main]
private lemma main
  {p q : α → Prop}
-- given
  (h : ∀ x y, q x → q y) :
-- imply
  (∀ x, p x → q x) ↔ ((∃ x, p x) → ∃ x, q x) :=
-- proof
  ⟨Imp.Any.of.Imp, fun h' => Imp.of.Imp.Any.given h' h⟩


-- created on 2026-09-27
