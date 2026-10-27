import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.Section36.Part14
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory Set FullyRelativeCapProduct
open Set FullyRelativeCapProduct


namespace FullyRelativeCapProduct

/--
[absNbhdExcisionInverse_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean)
-/
@[path]
lemma absNbhdExcisionInverse_compatible
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {K : Set X}
  {U₁ U₂ : CechCohomology.OpenNeighborhoods K}
  {n : ℕ}
  {y : (relSingularHomology R X Kᶜ n : Type _)}
-- given
  (h : U₁ ≤ U₂) :
-- imply
  excisionInverseHomol R X K U₁.1 U₁.2 n y = absNbhdHomologyIncl R U₁ U₂ h n (excisionInverseHomol R X K U₂.1 U₂.2 n y) := by
-- proof
  classical
  simp only [absNbhdHomologyIncl, LinearMap.comp_apply]
  congr 1
  simp only [excisionInverseHomol]
  haveI := excisionForwardHomol_isIso R X K U₂.1 U₂.2 n
  change y = (inv (excisionForwardHomol R X K U₂.1 n) ≫ excisionForwardHomol R X K U₂.1 n).hom y
  rw [IsIso.inv_hom_id]
  rfl

end FullyRelativeCapProduct

namespace FullyRelativeCapProduct

/--
[absExcisionForward_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean)
-/
@[path]
lemma absExcisionForward_compatible
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {K : Set X}
  {U₁ U₂ : CechCohomology.OpenNeighborhoods K}
  {q : ℕ}
  {w : (relSingularHomology R (TopCat.of ↑U₂.1.1) (Subtype.val ⁻¹' Kᶜ) q : Type _)}
-- given
  (h : U₁ ≤ U₂) :
-- imply
  (excisionForwardHomol R X K U₂.1 q).hom w = (excisionForwardHomol R X K U₁.1 q).hom (absNbhdHomologyIncl R U₁ U₂ h q w) := by
-- proof
  classical
  simp only [absNbhdHomologyIncl, LinearMap.comp_apply]
  simp only [excisionInverseHomol]
  haveI := excisionForwardHomol_isIso R X K U₁.1 U₁.2 q
  change (excisionForwardHomol R X K U₂.1 q).hom w =
    (excisionForwardHomol R X K U₁.1 q).hom
      ((inv (excisionForwardHomol R X K U₁.1 q)).hom
        ((excisionForwardHomol R X K U₂.1 q).hom w))
  conv_rhs => rw [show (inv (excisionForwardHomol R X K U₁.1 q)).hom
    ((excisionForwardHomol R X K U₂.1 q).hom w) =
    (excisionForwardHomol R X K U₂.1 q ≫ inv (excisionForwardHomol R X K U₁.1 q)).hom w
    from rfl]
  rw [show (excisionForwardHomol R X K U₁.1 q).hom
    ((excisionForwardHomol R X K U₂.1 q ≫ inv (excisionForwardHomol R X K U₁.1 q)).hom w) =
    (excisionForwardHomol R X K U₂.1 q ≫ inv (excisionForwardHomol R X K U₁.1 q) ≫
      excisionForwardHomol R X K U₁.1 q).hom w from rfl]
  simp only [IsIso.inv_hom_id, Category.comp_id]

end FullyRelativeCapProduct

/--
[absNbhdExcisionInverseHomol_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean)
-/
@[path]
lemma absNbhdExcisionInverseHomol_compatible
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {S : Set X}
  {U₁ U₂ : CechCohomology.OpenNeighborhoods S}
  {n : ℕ}
  {y : (relSingularHomology R X Sᶜ n : Type _)}
-- given
  (h : U₁ ≤ U₂) :
-- imply
  excisionInverseHomol R X S U₁.1 U₁.2 n y = absNbhdHomologyInclusion R X S U₁ U₂ h n (excisionInverseHomol R X S U₂.1 U₂.2 n y) := by
-- proof
  classical
  simp only [absNbhdHomologyInclusion, LinearMap.comp_apply]
  congr 1
  simp only [excisionInverseHomol]
  haveI := excisionForwardHomol_isIso R X S U₂.1 U₂.2 n
  change y = (inv (excisionForwardHomol R X S U₂.1 n) ≫ excisionForwardHomol R X S U₂.1 n).hom y
  rw [IsIso.inv_hom_id]
  rfl

/--
[absNbhdInclusionForwardHomol_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean)
-/
@[path]
lemma absNbhdInclusionForwardHomol_compatible
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {S : Set X}
  {U₁ U₂ : CechCohomology.OpenNeighborhoods S}
  {q : ℕ}
  {w : (relSingularHomology R (TopCat.of ↑U₂.1.1) (Subtype.val ⁻¹' Sᶜ) q : Type _)}
-- given
  (h : U₁ ≤ U₂) :
-- imply
  inclusionForwardHomol R X S U₂ q w = inclusionForwardHomol R X S U₁ q (absNbhdHomologyInclusion R X S U₁ U₂ h q w) := by
-- proof
  classical
  simp only [inclusionForwardHomol, absNbhdHomologyInclusion, LinearMap.comp_apply]
  simp only [excisionInverseHomol]
  haveI := excisionForwardHomol_isIso R X S U₁.1 U₁.2 q
  change (excisionForwardHomol R X S U₂.1 q).hom w =
    (excisionForwardHomol R X S U₁.1 q).hom
      ((inv (excisionForwardHomol R X S U₁.1 q)).hom
        ((excisionForwardHomol R X S U₂.1 q).hom w))
  conv_rhs => rw [show (inv (excisionForwardHomol R X S U₁.1 q)).hom
    ((excisionForwardHomol R X S U₂.1 q).hom w) =
    (excisionForwardHomol R X S U₂.1 q ≫ inv (excisionForwardHomol R X S U₁.1 q)).hom w
    from rfl]
  rw [show (excisionForwardHomol R X S U₁.1 q).hom
    ((excisionForwardHomol R X S U₂.1 q ≫ inv (excisionForwardHomol R X S U₁.1 q)).hom w) =
    (excisionForwardHomol R X S U₂.1 q ≫ inv (excisionForwardHomol R X S U₁.1 q) ≫
      excisionForwardHomol R X S U₁.1 q).hom w from rfl]
  simp only [IsIso.inv_hom_id, Category.comp_id]
/-- Naturality of the composite "inclusion-cap-excise" cap rung across two
neighbourhoods `U₁ ≤ U₂`, combining the three naturality lemmas above.
Used to descend the cap rung to the Čech direct limit. -/

/--
[subtypeIncl_factor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean)
-/
@[path]
private lemma subtypeIncl_factor_eq
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {A B : Set X}
-- given
  (h : A ⊆ B) :
-- imply
  subtypeIncl X A = subsetInclusion X A B h ≫ subtypeIncl X B := by
-- proof
  apply FullyRelativeCapProduct.subtypeIncl_factor R X A B h

/--
[tripleIncl_comm_topcat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean)
-/
@[path]
private lemma tripleIncl_comm_topcat_eq
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {K L : Set X} :
-- imply
  subtypeIncl (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) ≫ subtypeIncl X Lᶜ = complToComplement X K L ≫ subtypeIncl X Kᶜ := by
-- proof
  apply FullyRelativeCapProduct.tripleIncl_comm_topcat R X K L

/--
[tripleIncl_comm_chain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean)
-/
@[path]
private lemma tripleIncl_comm_chain_eq
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {K L : Set X} :
-- imply
  inclChainMap R (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) ≫ ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map (subtypeIncl X Lᶜ) = ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map (complToComplement X K L) ≫ inclChainMap R X Kᶜ := by
-- proof
  apply FullyRelativeCapProduct.tripleIncl_comm_chain R X K L

/--
[restriction_comm_chain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean)
-/
@[path]
private lemma restriction_comm_chain_eq
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {K L : Set X}
-- given
  (h : (Kᶜ : Set X) ⊆ Lᶜ) :
-- imply
  inclChainMap R X Kᶜ ≫ 𝟙 _ = ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map (subsetInclusion X Kᶜ Lᶜ h) ≫ inclChainMap R X Lᶜ := by
-- proof
  apply FullyRelativeCapProduct.restriction_comm_chain R X K L h

/--
[tripleInclChainMap_comp_restrictionChainMap_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean)
-/
@[path]
private lemma tripleInclChainMap_comp_restrictionChainMap_eq_zero_eq
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {K L : Set X}
-- given
  (h : (Kᶜ : Set X) ⊆ Lᶜ) :
-- imply
  tripleInclChainMap R X K L ≫ restrictionChainMap R X K L h = 0 := by
-- proof
  apply FullyRelativeCapProduct.tripleInclChainMap_comp_restrictionChainMap_eq_zero R X K L h

/--
[excisionPairIncl_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean)
-/
@[path]
private lemma excisionPairIncl_comm_eq
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {K : Set X}
  {U : TopologicalSpace.Opens X} :
-- imply
  inclChainMap R (TopCat.of ↑U.1) (Subtype.val ⁻¹' Kᶜ) ≫ ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map (excisionOpenIncl X U) = ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map (excisionSubspaceIncl X K U) ≫ inclChainMap R X Kᶜ := by
-- proof
  apply FullyRelativeCapProduct.excisionPairIncl_comm R X K U

/--
[excisionPairChainMap_quasiIsoAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean)
-/
@[path]
private lemma excisionPairChainMap_quasiIsoAt_eq
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {K : Set X}
  {U : TopologicalSpace.Opens X}
  {n : ℕ}
-- given
  (hK : K ⊆ ↑U) :
-- imply
  QuasiIsoAt (excisionPairChainMap R X K U) n := by
-- proof
  apply FullyRelativeCapProduct.excisionPairChainMap_quasiIsoAt R X K U hK n

/--
[excisionForwardHomol_isIso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean)
-/
@[path]
private lemma excisionForwardHomol_isIso_eq
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {K : Set X}
  {U : TopologicalSpace.Opens X}
  {n : ℕ}
-- given
  (hK : K ⊆ ↑U) :
-- imply
  IsIso (excisionForwardHomol R X K U n) := by
-- proof
  apply FullyRelativeCapProduct.excisionForwardHomol_isIso R X K U hK n

/--
[localityIncl_comm_topcat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean)
-/
@[path]
private lemma localityIncl_comm_topcat_eq
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {K L : Set X}
  {pair : OpenNbhdPair K L} :
-- imply
  subtypeIncl (TopCat.of ↑(pair.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ≫ localityBigIncl X L pair = localitySubIncl X K L pair ≫ subtypeIncl (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) := by
-- proof
  apply FullyRelativeCapProduct.localityIncl_comm_topcat R X K L pair

/--
[localityIncl_comm_chain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean)
-/
@[path]
private lemma localityIncl_comm_chain_eq
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {K L : Set X}
  {pair : OpenNbhdPair K L} :
-- imply
  inclChainMap R (TopCat.of ↑(pair.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ≫ ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map (localityBigIncl X L pair) = ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map (localitySubIncl X K L pair) ≫ inclChainMap R (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) := by
-- proof
  apply FullyRelativeCapProduct.localityIncl_comm_chain R X K L pair

/--
[nbhdIncl_comm_topcat_n](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean)
-/
@[path]
private lemma nbhdIncl_comm_topcat_n_eq
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {K L : Set X}
  {pair₁ pair₂ : OpenNbhdPair K L}
-- given
  (h : pair₁ ≤ pair₂) :
-- imply
  subtypeIncl (TopCat.of ↑pair₂.U.1) (Subtype.val ⁻¹' Kᶜ) ≫ opensInclusion pair₁.U pair₂.U h.1 = nbhdSubIncl_n pair₁ pair₂ h ≫ subtypeIncl (TopCat.of ↑pair₁.U.1) (Subtype.val ⁻¹' Kᶜ) := by
-- proof
  apply FullyRelativeCapProduct.nbhdIncl_comm_topcat_n R pair₁ pair₂ h

/--
[nbhdIncl_comm_chain_n](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean)
-/
@[path]
private lemma nbhdIncl_comm_chain_n_eq
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {K L : Set X}
  {pair₁ pair₂ : OpenNbhdPair K L}
-- given
  (h : pair₁ ≤ pair₂) :
-- imply
  inclChainMap R (TopCat.of ↑pair₂.U.1) (Subtype.val ⁻¹' Kᶜ) ≫ ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map (opensInclusion pair₁.U pair₂.U h.1) = ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map (nbhdSubIncl_n pair₁ pair₂ h) ≫ inclChainMap R (TopCat.of ↑pair₁.U.1) (Subtype.val ⁻¹' Kᶜ) := by
-- proof
  apply FullyRelativeCapProduct.nbhdIncl_comm_chain_n R pair₁ pair₂ h

/--
[nbhdIncl_comm_topcat_q](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean)
-/
@[path]
private lemma nbhdIncl_comm_topcat_q_eq
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {K L : Set X}
  {pair₁ pair₂ : OpenNbhdPair K L}
-- given
  (h : pair₁ ≤ pair₂) :
-- imply
  subtypeIncl (TopCat.of ↑(pair₂.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ≫ nbhdBigIncl_q pair₁ pair₂ h = nbhdSubIncl_q pair₁ pair₂ h ≫ subtypeIncl (TopCat.of ↑(pair₁.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) := by
-- proof
  apply FullyRelativeCapProduct.nbhdIncl_comm_topcat_q R pair₁ pair₂ h

/--
[nbhdIncl_comm_chain_q](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean)
-/
@[path]
private lemma nbhdIncl_comm_chain_q_eq
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {K L : Set X}
  {pair₁ pair₂ : OpenNbhdPair K L}
-- given
  (h : pair₁ ≤ pair₂) :
-- imply
  inclChainMap R (TopCat.of ↑(pair₂.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ≫ ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map (nbhdBigIncl_q pair₁ pair₂ h) = ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map (nbhdSubIncl_q pair₁ pair₂ h) ≫ inclChainMap R (TopCat.of ↑(pair₁.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) := by
-- proof
  apply FullyRelativeCapProduct.nbhdIncl_comm_chain_q R pair₁ pair₂ h


-- created on 2026-10-23
