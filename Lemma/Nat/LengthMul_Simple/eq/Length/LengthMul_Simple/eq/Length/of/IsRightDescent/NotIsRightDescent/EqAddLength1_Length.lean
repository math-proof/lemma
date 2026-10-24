import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.StrongExchangeProof
open CoxeterBruhat


namespace Definitions
end Definitions
namespace CoxeterBruhat

/--
[exchange_length_analysis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/StrongExchangeProof.lean)
-/
@[path]
private lemma exchange_length_analysis
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {v w : W}
  {i : B}
-- given
  (hcover : cs.length v + 1 = cs.length w)
  (hv_not_desc : ¬cs.IsRightDescent v i)
  (hw_desc : cs.IsRightDescent w i) :
-- imply
  cs.length (w * cs.simple i) = cs.length v ∧ cs.length (v * cs.simple i) = cs.length w := by
-- proof
  constructor
  · rcases cs.length_mul_simple w i with h | h
    · exfalso; exact not_lt.mpr (by omega) hw_desc
    · omega
  · rcases cs.length_mul_simple v i with h | h
    · omega
    · exfalso; exact hv_not_desc (by unfold CoxeterSystem.IsRightDescent; omega)

end CoxeterBruhat

namespace CoxeterBruhat

/--
[strong_exchange_of_reflection_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/StrongExchangeProof.lean)
-/
@[path]
private lemma strong_exchange_of_reflection_id
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
-- given
  (hid : ReflectionIdentificationHyp cs) :
-- imply
  StrongExchangeForBruhat cs := by
-- proof
  intro v w t ht hvt hcover i hv_not_desc hw_desc
  have := hid.identify v w t ht hvt hcover i hv_not_desc hw_desc
  rwa [this] at hvt

end CoxeterBruhat


-- created on 2026-10-24
