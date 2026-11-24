module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.TheoryOfComputation.code.LadderNSPACE.Part3
open Computability TuringMachine


public section

namespace SpaceComplexity

/--
[LADDER_DFA_in_SPACE_n2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LadderPSPACE.lean)
-/
@[path]
theorem LADDER_DFA_in_SPACE_n2
  {α : Type}
  {σ : Type}
  [Fintype α]
  [DecidableEq α]
  [Fintype σ]
  [DecidableEq σ]
  {B : DFA α σ} :
-- imply
  InSPACE (fun n => n ^ 2) (LADDER_DFA_Lang B) :=
-- proof
  savitch id (fun n => Nat.le_refl n) (LADDER_DFA_Lang B) (LADDER_DFA_in_NSPACE_n B)

end SpaceComplexity

namespace SpaceComplexity

/--
[LADDER_DFA_in_PSPACE](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LadderPSPACE.lean)
-/
@[path]
theorem LADDER_DFA_in_PSPACE
  {α : Type}
  {σ : Type}
  [Fintype α]
  [DecidableEq α]
  [Fintype σ]
  [DecidableEq σ]
  {B : DFA α σ} :
-- imply
  InPSPACE (LADDER_DFA_Lang B) :=
-- proof
  ⟨2, LADDER_DFA_in_SPACE_n2 B⟩

end SpaceComplexity


-- created on 2026-10-23
