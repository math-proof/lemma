import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.AlderTotient
open ArithmeticFunction


namespace ArithmeticFunction

/--
[alderTotientTwo_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/AlderTotient.lean)
-/
@[path]
lemma alderTotientTwo_apply
  {k : ℕ} :
-- imply
  alderTotientTwo k =
      ((Finset.range k).filter fun r =>
        Nat.Coprime k r ∧ Nat.Coprime k (2 * r + 1)).card :=
-- proof
  rfl

end ArithmeticFunction

namespace ArithmeticFunction

/--
[alderTotientTwo_succ_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/AlderTotient.lean)
-/
@[path]
lemma alderTotientTwo_succ_apply
  {k : ℕ} :
-- imply
  alderTotientTwo (k + 1) =
      ((Finset.range (k + 1)).filter fun r =>
        Nat.Coprime r (k + 1) ∧ Nat.Coprime (2 * r + 1) (k + 1)).card := by
-- proof
  have h := alderTotientTwo_apply (k + 1)
  have heq :
    ((Finset.range (k + 1)).filter fun r =>
      Nat.Coprime (k + 1) r ∧ Nat.Coprime (k + 1) (2 * r + 1)) =
      ((Finset.range (k + 1)).filter fun r =>
        Nat.Coprime r (k + 1) ∧ Nat.Coprime (2 * r + 1) (k + 1)) := by
    apply Finset.filter_congr
    intro r _
    exact ⟨fun ⟨h1, h2⟩ => ⟨Nat.coprime_comm.mp h1, Nat.coprime_comm.mp h2⟩,
      fun ⟨h1, h2⟩ => ⟨Nat.coprime_comm.mpr h1, Nat.coprime_comm.mpr h2⟩⟩
  rw [h, heq]

end ArithmeticFunction

namespace ArithmeticFunction

/--
[alderTotientTwo_succ_Iic_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/AlderTotient.lean)
-/
@[path]
lemma alderTotientTwo_succ_Iic_apply
  {k : ℕ} :
-- imply
  alderTotientTwo (k + 1) =
      ((Finset.Iic k).filter fun r =>
        Nat.Coprime r (k + 1) ∧ Nat.Coprime (2 * r + 1) (k + 1)).card := by
-- proof
  rw [alderTotientTwo_succ_apply]
  congr 1
  ext r
  simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Iic]

end ArithmeticFunction

namespace ArithmeticFunction

/--
[alderTotientTwo_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/AlderTotient.lean)
-/
@[path]
lemma alderTotientTwo_zero
  :
-- imply
  alderTotientTwo 0 = 0 :=
-- proof
  rfl

end ArithmeticFunction

namespace ArithmeticFunction

/--
[alderTotientTwo_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/AlderTotient.lean)
-/
@[path]
lemma alderTotientTwo_one
  :
-- imply
  alderTotientTwo 1 = 1 :=
-- proof
  rfl

end ArithmeticFunction

namespace ArithmeticFunction

/--
[alderTotientTwo_le_totient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/AlderTotient.lean)
-/
@[path]
lemma alderTotientTwo_le_totient
  {k : ℕ} :
-- imply
  alderTotientTwo k ≤ Nat.totient k := by
-- proof
  rw [alderTotientTwo_apply, Nat.totient_eq_card_coprime k]
  apply Finset.card_le_card
  intro r hr
  simp only [Finset.mem_filter] at hr ⊢
  obtain ⟨hmem, h1, _⟩ := hr
  exact ⟨hmem, h1⟩

end ArithmeticFunction


-- created on 2026-10-20
-- updated on 2026-10-23
