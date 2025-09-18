import Lemma.Basic


@[main, comm, mp 8, mpr 4]
private lemma left
  [Add α]
  [LE α]
  [AddLeftReflectLE α]
  [AddLeftMono α]
-- given
  (a b c : α) :
-- imply
  a + b ≤ a + c ↔ b ≤ c :=
-- proof
  -- add_le_add_iff_left a
  ⟨le_of_add_le_add_left, (add_le_add_left · a)⟩


@[main, comm, mp 8, mpr 4]
private lemma main
  [Add α]
  [LE α]
  [AddRightReflectLE α]
  [AddRightMono α]
-- given
  (a b c : α) :
-- imply
  b + a ≤ c + a ↔ b ≤ c :=
-- proof
  -- add_le_add_iff_right a
  ⟨le_of_add_le_add_right, (add_le_add_right · a)⟩


-- created on 2025-07-29
