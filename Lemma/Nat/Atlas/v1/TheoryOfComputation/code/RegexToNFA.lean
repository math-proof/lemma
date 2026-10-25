import Mathlib
import sympy.Basic
import Def.v1.Atlas.TheoryOfComputation.code.RegularLanguages
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.RegularLanguages
open Computability Language


namespace RegularLanguages

/--
[foldl_sink](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegexToNFA.lean)
-/
@[path]
lemma foldl_sink
  [DecidableEq α]
  {a₀ : α}
  {l : List α} :
-- imply
  List.foldl (fun (s : Fin 3) (c : α) => if s = 0 ∧ c = a₀ then 1 else 2) 2 l = 2 := by
-- proof
  induction l with
  | nil => rfl
  | cons _ _ ih =>
    simp only [List.foldl_cons, show ¬((2 : Fin 3) = 0) from by omega, false_and, ↓reduceIte]
    exact ih

end RegularLanguages

namespace RegularLanguages

/--
[foldl_bool_sink](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegexToNFA.lean)
-/
@[path]
lemma foldl_bool_sink
  {l : List α} :
-- imply
  List.foldl (fun (_ : Bool) (_ : α) => false) false l = false := by
-- proof
  induction l with | nil => rfl | cons _ _ ih => exact ih

end RegularLanguages

namespace RegularLanguages

/--
[isRegular_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegexToNFA.lean)
-/
@[path]
lemma isRegular_empty
-- imply
  (0 : Language α).IsRegular := by
-- proof
  refine ⟨Unit, inferInstance, ⟨fun _ _ => (), (), ∅⟩, ?_⟩
  ext w; constructor
  · intro h; exfalso; rw [DFA.mem_accepts] at h; exact absurd h (Set.notMem_empty _)
  · intro h; exfalso; exact absurd h (by change w ∉ (∅ : Set _); exact Set.notMem_empty _)

end RegularLanguages

namespace RegularLanguages

/--
[isRegular_epsilon](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegexToNFA.lean)
-/
@[path]
lemma isRegular_epsilon
-- imply
  (1 : Language α).IsRegular := by
-- proof
  refine ⟨Bool, inferInstance, ⟨fun _ _ => false, true, {true}⟩, ?_⟩
  ext w; rw [DFA.mem_accepts]; simp only [Set.mem_singleton_iff, DFA.eval, DFA.evalFrom]
  rw [Language.mem_one]
  constructor
  · intro h; cases w with
    | nil => rfl
    | cons a t =>
      exfalso; simp only [List.foldl_cons] at h
      rw [foldl_bool_sink] at h; exact Bool.false_ne_true h
  · rintro rfl; rfl

end RegularLanguages

namespace RegularLanguages

/--
[isRegular_char](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegexToNFA.lean)
-/
@[path]
lemma isRegular_char
  [DecidableEq α]
  {a₀ : α} :
-- imply
  ({[a₀]} : Language α).IsRegular := by
-- proof
  let step : Fin 3 → α → Fin 3 := fun s a => if s = 0 ∧ a = a₀ then 1 else 2
  refine ⟨Fin 3, inferInstance, ⟨step, 0, {1}⟩, ?_⟩
  ext w
  simp only [DFA.mem_accepts, Set.mem_singleton_iff, DFA.eval, DFA.evalFrom]
  constructor
  · intro h; cases w with
    | nil => simp only [List.foldl_nil] at h; omega
    | cons b t =>
      simp only [List.foldl_cons, step] at h
      split_ifs at h with hba
      · obtain ⟨-, rfl⟩ := hba
        cases t with
        | nil => rfl
        | cons d u =>
          exfalso
          simp only [List.foldl_cons, show ¬((1 : Fin 3) = 0) from by omega,
            false_and, ↓reduceIte] at h
          rw [foldl_sink] at h; omega
      · exfalso; rw [foldl_sink] at h; omega
  · intro h; rw [h]; show List.foldl step (step 0 a₀) [] = 1
    simp [step]

end RegularLanguages

namespace RegularLanguages

/--
[regex_language_isRegular](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegexToNFA.lean)
-/
@[path]
lemma regex_language_isRegular
  [DecidableEq α]
  {R : RegularExpression α} :
-- imply
  R.matches'.IsRegular := by
-- proof
  induction R with
  | zero => exact isRegular_empty
  | epsilon => exact isRegular_epsilon
  | char a => exact isRegular_char a
  | plus P Q ihP ihQ =>
    simp only [RegularExpression.matches']
    exact ihP.add ihQ
  | comp P Q ihP ihQ =>
    simp only [RegularExpression.matches']
    exact regular_concat ihP ihQ
  | star P ihP =>
    simp only [RegularExpression.matches']
    exact regular_star ihP

end RegularLanguages


-- created on 2026-10-23
