import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Building.ThicknessHypAssembly
open ChamberComplex AptIsCoxeterProof


namespace AptIsCoxeterProof

/--
[apt_is_coxeter_from_foldings'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ThicknessHypAssembly.lean)
-/
@[path]
lemma apt_is_coxeter_from_foldings'
  {V : Type}
  [DecidableEq V]
  {K : ChamberComplex V}
  {pre : PreApartmentData K}
  {tits_thm : TitsTheoremHyp V}
  {A : SimplicialComplex V}
-- given
  (hThick : K.IsThick)
  (hA : A ∈ pre.apartments) :
-- imply
  ∃ (B_idx : Type) (M : CoxeterMatrix B_idx) (cc : ChamberComplex V), cc.toSimplicialComplex = A ∧ ∃ (φ : Finset V → M.Group), (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧ (∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w) ∧ (∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) ∧ cc.IsThin :=
-- proof
  apt_is_coxeter_from_foldings K hThick pre tits_thm thickness_hyp A hA

end AptIsCoxeterProof

namespace AptIsCoxeterProof

/--
[PreApartmentData.toApartmentSystem_apartments'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ThicknessHypAssembly.lean)
-/
@[path]
lemma PreApartmentData.toApartmentSystem_apartments'
  {V : Type}
  [DecidableEq V]
  {K : ChamberComplex V}
  {pre : PreApartmentData K}
  {tits_thm : TitsTheoremHyp V}
-- given
  (hThick : K.IsThick) :
-- imply
  (pre.toApartmentSystem' hThick tits_thm).apartments = pre.apartments :=
-- proof
  rfl

end AptIsCoxeterProof

/--
[thickness_hyp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ThicknessHypAssembly.lean)
-/
@[path]
private lemma thickness_hyp_eq
  {V : Type}
  [DecidableEq V] :
-- imply
  ThicknessImpliesAptStructureHyp V := by
-- proof
  apply AptIsCoxeterProof.thickness_hyp


-- created on 2026-10-23
