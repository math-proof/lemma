import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.Building.AptIsCoxeterUnconditional
open ChamberComplex


namespace AptIsCoxeterProof

/--
[apt_sufficient_foldings](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AptSufficientFoldings.lean)
-/
@[path]
lemma apt_sufficient_foldings
  {V : Type}
  [DecidableEq V]
  {K : ChamberComplex V}
  {pre : PreApartmentData K}
  {A : SimplicialComplex V}
-- given
  (hThick : K.IsThick)
  (hA : A ∈ pre.apartments) :
-- imply
  ∃ (cc : ChamberComplex V), cc.toSimplicialComplex = A ∧ cc.IsThin ∧ HasSufficientFoldings cc :=
-- proof
  thickness_hyp K hThick pre A hA

end AptIsCoxeterProof


-- created on 2026-10-23
