import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.IsCompactIntegers
import Lemma.Int.IsOpenUnitBall
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Nat
open Int


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

@[path]
private lemma main:
-- imply
  IsCompact {x : F | Valued.v x = 1} := by
-- proof
  suffices hclosed : IsClosed {x : F | Valued.v x = 1} by
    exact (Nat.IsCompactIntegers v).of_isClosed_subset hclosed (fun x hx => le_of_eq hx)
  have h1 : IsClosed {x : F | Valued.v x ≤ 1} := (Nat.IsCompactIntegers v).isClosed
  have h2 : IsClosed {x : F | Valued.v x < (1 : WithZero (Multiplicative ℤ))}ᶜ := (Int.IsOpenUnitBall v).isClosed_compl
  convert h1.inter h2 using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_lt]
  exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩

end LocalGL2.Kirillov

end


-- created on 2026-10-25
