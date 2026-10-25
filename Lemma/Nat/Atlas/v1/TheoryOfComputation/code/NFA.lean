import Mathlib
import sympy.Basic
import Def.v1.Atlas.TheoryOfComputation.code.NFA
open Computability Set Sipser Sipser.NFA


namespace Sipser.NFA

variable {σ : Type*} [DecidableEq Q]
/--
[language_eq_toεNFA_accepts](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NFA.lean)
-/
@[path]
underlying Mathlib `εNFA`. -/
lemma language_eq_toεNFA_accepts (M : NFA Q σ) :
  M.language = εNFA.accepts M.toεNFA :=
  rfl

end Sipser.NFA

namespace Sipser.NFA

/--
[language_isRegular](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NFA.lean)
-/
@[path]
lemma language_isRegular
  [DecidableEq Q]
  [Fintype Q]
  {M : NFA Q σ} :
-- imply
  M.language.IsRegular := by
-- proof
  rw [language_eq_toεNFA_accepts, Language.isRegular_iff]
  exact ⟨Set Q, inferInstance, M.toεNFA.toNFA.toDFA,
    by simp [εNFA.toNFA_correct, NFA.toDFA_correct]⟩
namespace NFAtoDFA
open Computability
end NFAtoDFA

end Sipser.NFA

/--
[language_eq_to](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NFA.lean)
-/
@[path]
private lemma language_eq_to_eq
  [DecidableEq Q]
  {M : NFA Q σ} :
-- imply
  M.language = εNFA.accepts M.toεNFA := by
-- proof
  apply Sipser.NFA.language_eq_to M


-- created on 2026-10-23
