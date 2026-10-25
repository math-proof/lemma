import Mathlib
import Instance.Analysis.Section_2_3_api
import Def.Analysis.Section_2_epilogue


namespace PeanoAxioms

/-- One can map the Mathlib natural numbers into any other structure obeying the Peano axioms. -/
abbrev natCast (P : PeanoAxioms) : ℕ → P.Nat := fun n ↦ match n with
  | Nat.zero => P.zero
  | Nat.succ n => P.succ (natCast P n)

end PeanoAxioms
