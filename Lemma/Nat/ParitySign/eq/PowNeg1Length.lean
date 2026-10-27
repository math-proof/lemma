import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.ParitySign
open CoxeterSystem
open List


namespace Definitions
end Definitions
namespace CoxeterSystem

/--
[paritySign_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParitySign.lean)
-/
@[path]
private lemma paritySign_eq
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {w : W} :
-- imply
  cs.paritySign w = (-1 : ℤˣ) ^ cs.length w :=
-- proof
  rfl

end CoxeterSystem

/--
[neg_one_units_pow_eq_of_mod_two_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParitySign.lean)
-/
@[path]
private lemma neg_one_units_pow_eq_of_mod_two_eq_eq
  {a b : ℕ}
-- given
  (h : a % 2 = b % 2) :
-- imply
  ((-1 : ℤˣ) ^ a) = ((-1 : ℤˣ) ^ b) := by
-- proof
  apply CoxeterSystem.neg_one_units_pow_eq_of_mod_two_eq h


-- created on 2026-10-24
