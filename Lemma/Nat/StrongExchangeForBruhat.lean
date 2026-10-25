import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.ReflectionIdentificationGenuine
open CoxeterReflectionId


namespace Definitions
end Definitions
namespace CoxeterReflectionId

/--
[reflection_identification_genuine](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ReflectionIdentificationGenuine.lean)
-/
@[path]
private lemma reflection_identification_genuine
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {bridge : InversionDifferenceBridgeHyp cs} :
-- imply
  CoxeterBruhat.ReflectionIdentificationHyp cs where identify :=
-- proof
  bridge.identify_from_inversions

end CoxeterReflectionId

namespace CoxeterReflectionId

/--
[strong_exchange_from_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ReflectionIdentificationGenuine.lean)
-/
@[path]
private lemma strong_exchange_from_bridge
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {bridge : InversionDifferenceBridgeHyp cs} :
-- imply
  CoxeterBruhat.StrongExchangeForBruhat cs :=
-- proof
  CoxeterBruhat.strong_exchange_of_reflection_id cs
    (reflection_identification_genuine bridge)

end CoxeterReflectionId


-- created on 2026-10-24
