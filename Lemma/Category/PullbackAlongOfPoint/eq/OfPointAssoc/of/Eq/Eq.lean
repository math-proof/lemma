import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.AlgebraicGeometry.RelEffCartierDivOfPoint
import Lemma.Int.P2MUtil

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RelEffCartierDiv

/--
[AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint.lean)
-/

private lemma  isPullback_graphOver_comp
  {𝒞 S : Scheme.{u}}
  (f : 𝒞 ⟶ S)
  {T T' : Scheme.{u}}
  {g : T ⟶ S}
  {g' : T' ⟶ S}
  [IsSeparated f] (a : T' ⟶ 𝒞) (ha : a ≫ f = g')
  (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
  IsPullback (graphOver f (φ ≫ a) (by rw [Category.assoc, ha, hφ])) φ
    (mapOnProdOver f φ hφ) (graphOver f a ha) := by
  have s : IsPullback (graphOver f (φ ≫ a) (by rw [Category.assoc, ha, hφ]) ≫ pullback.snd f g)
    φ φ (graphOver f a ha ≫ pullback.snd f g') := by
    rw [graphOver_snd, graphOver_snd]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  refine IsPullback.of_right s ?_ (isPullback_mapOnProdOver f φ hφ).flip
  apply pullback.hom_ext <;> simp
@[path]
private lemma main
  {𝒞 S : Scheme.{u}}
  {f : 𝒞 ⟶ S} [IsSeparated f]
  {T T' : Scheme.{u}}
  {g : T ⟶ S}
  {g' : T' ⟶ S}
  {a : T' ⟶ 𝒞}
  {φ : T ⟶ T'}
-- given
  (ha : a ≫ f = g')
  (hφ : φ ≫ g' = g) :
-- imply
  (RelEffCartierDiv.ofPoint f a ha).pullbackAlong φ hφ =
      RelEffCartierDiv.ofPoint f (φ ≫ a) (by rw [Category.assoc, ha, hφ]) := by
-- proof
  refine RelEffCartierDiv.ext ?_
  change (graphOver f a ha).ker.comap (mapOnProdOver f φ hφ) = (graphOver f (φ ≫ a) _).ker
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← (isPullback_graphOver_comp
      f a ha φ hφ).isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]


-- created on 2026-10-23
