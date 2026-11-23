module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Inductive.v1.Atlas.TheoryOfComputation.code.CFGtoPDA.Part2
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.CFGtoPDA
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.CFLInterRegular
public import Def.v1.Atlas.TheoryOfComputation.code.CFLInterRegular

public section


namespace CFGPDAEquiv

/--
[cfl_iff_pda_recognizes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGPDAEquiv.lean)
-/
@[path]
public theorem cfl_iff_pda_recognizes
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
