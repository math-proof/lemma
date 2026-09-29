import Lemma.Bool.Imp_And.of.Imp.And.subst.Bool
open Bool


@[main]
private lemma main
  {p c : Prop} [Decidable c]
  {x z : α}
  {P : α → Prop} :
-- imply
  (p ∧ c → P (if c then x else z)) ↔ (p ∧ c → P x) := by
-- proof
  refine ⟨fun h hpc => ?_, Imp_And.of.Imp.And.subst.Bool.given⟩
  have h' := h hpc
  rwa [if_pos hpc.2] at h'


-- created on 2026-09-27
