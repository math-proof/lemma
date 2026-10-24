import Mathlib

set_option autoImplicit false

universe u

open CategoryTheory

namespace groupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

noncomputable abbrev inflation (M : Rep k G) (S : Subgroup G) [S.Normal] :
    H1 (M.quotientToInvariants S) ⟶ H1 M :=
  groupCohomology.map (QuotientGroup.mk' S) (Rep.ofHom (M.ρ.quotientToInvariants_lift S)) 1

lemma inflation_eq_H1InfRes_f (M : Rep k G) (S : Subgroup G) [S.Normal] :
    inflation M S = (H1InfRes M S).f :=
  rfl

noncomputable def inflationImage (M : Rep k G) (S : Subgroup G) [S.Normal] :
    Submodule k (H1 M) :=
  LinearMap.range (inflation M S).hom

lemma mem_inflationImage_iff (M : Rep k G) (S : Subgroup G) [S.Normal] (x : H1 M) :
    x ∈ inflationImage M S ↔ ∃ y, (inflation M S).hom y = x :=
  Iff.rfl

lemma inflation_mem_inflationImage (M : Rep k G) (S : Subgroup G) [S.Normal]
    (y : H1 (M.quotientToInvariants S)) :
    (inflation M S).hom y ∈ inflationImage M S :=
  LinearMap.mem_range_self _ y

noncomputable def locallyConstantClasses (M : Rep k G) : Submodule k (H1 M) :=
  ⨆ S : {S : Subgroup G // S.Normal ∧ S.FiniteIndex},
    haveI : S.1.Normal := S.2.1
    inflationImage M S.1

lemma inflationImage_le_locallyConstantClasses (M : Rep k G) (S : Subgroup G) [hN : S.Normal]
    [hF : S.FiniteIndex] : inflationImage M S ≤ locallyConstantClasses M :=
  le_iSup (fun S : {S : Subgroup G // S.Normal ∧ S.FiniteIndex} =>
    haveI : S.1.Normal := S.2.1
    inflationImage M S.1) ⟨S, hN, hF⟩

lemma le_locallyConstantClasses_of_le_inflationImage (M : Rep k G) {L : Submodule k (H1 M)}
    {S : Subgroup G} [S.Normal] [S.FiniteIndex] (hL : L ≤ inflationImage M S) :
    L ≤ locallyConstantClasses M :=
  hL.trans (inflationImage_le_locallyConstantClasses M S)

end groupCohomology
