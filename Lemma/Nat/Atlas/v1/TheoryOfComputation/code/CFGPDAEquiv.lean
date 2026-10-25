import Mathlib
import sympy.Basic
import Inductive.v1.Atlas.TheoryOfComputation.code.CFGtoPDA.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.CFGtoPDA
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.CFLInterRegular
import Def.v1.Atlas.TheoryOfComputation.code.CFLInterRegular


namespace CFGPDAEquiv

/--
[cfl_iff_pda_recognizes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGPDAEquiv.lean)
-/
@[path]
lemma cfl_iff_pda_recognizes
  {α : Type u}
  {A : Language α} :
-- imply
  Language.IsContextFree A ↔ ∃ (σ : Type u) (γ : Type u) (M : PDA α σ γ), M.language = A := by
-- proof
  constructor
  ·
    exact cfl_recognized_by_pda A
  ·
    rintro ⟨σ, γ, M, rfl⟩
    exact pda_language_isContextFree M

end CFGPDAEquiv


-- created on 2026-10-23
