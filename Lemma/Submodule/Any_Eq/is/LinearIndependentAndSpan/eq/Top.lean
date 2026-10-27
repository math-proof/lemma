import Mathlib
import Initialize.Tactic.Attr.Basic
open Module


/--
[basis_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/VectorSpaces.lean)
-/
@[path]
private lemma main
  [Semiring R]
  [AddCommMonoid M]
  [Module R M]
  {v : ι → M} :
-- imply
  (∃ b : Basis ι R M, ⇑b = v) ↔ (LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤) := by
-- proof
  constructor
  ·
    rintro ⟨b, rfl⟩
    refine ⟨b.linearIndependent, b.span_eq⟩
  ·
    rintro ⟨hli, hsp⟩
    refine ⟨Basis.mk hli (le_of_eq hsp.symm), Basis.coe_mk hli _⟩


-- created on 2026-10-23
-- updated on 2026-10-26
