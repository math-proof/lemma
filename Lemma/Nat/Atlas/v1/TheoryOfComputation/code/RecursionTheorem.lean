import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TheoryOfComputation.code.RecursionTheorem
open RecursionTheorem


namespace RecursionTheorem

/--
[recursion_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RecursionTheorem.lean)
-/
@[path]
lemma recursion_theorem
  {C : TMCoding Γ}
  {t : C.TMIndex → C.TMIndex}
-- given
  (ht : C.IsComputable t) :
-- imply
  ∃ R : C.TMIndex, ∀ (w : List Γ), C.behavior R w = C.behavior (t R) w := by
-- proof
  let h : C.TMIndex → C.TMIndex := fun x => t (C.smn x x)
  have hh : C.IsComputable h :=
    C.isComputable_comp t (fun x => C.smn x x) ht C.isComputable_smn_diag
  obtain ⟨e₀, he₀⟩ := C.representable h hh
  exact ⟨C.smn e₀ e₀, he₀ e₀⟩

end RecursionTheorem

namespace RecursionTheorem

/--
[recursion_theorem_language](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RecursionTheorem.lean)
-/
@[path]
lemma recursion_theorem_language
  {C : TMCoding Γ}
  {t : C.TMIndex → C.TMIndex}
-- given
  (ht : C.IsComputable t) :
-- imply
  ∃ R : C.TMIndex, C.languageOf R = C.languageOf (t R) := by
-- proof
  obtain ⟨R, hR⟩ := recursion_theorem C t ht
  exact ⟨R, Set.ext fun w => by
    simp only [TMCoding.languageOf, Set.mem_setOf_eq, hR w]⟩

end RecursionTheorem


-- created on 2026-10-23
