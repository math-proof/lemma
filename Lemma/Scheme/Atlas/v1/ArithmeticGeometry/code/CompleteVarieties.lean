import Mathlib
import sympy.Basic
import Instance.v1.Atlas.ArithmeticGeometry.code.CompleteVarieties
open AlgebraicGeometry in IsCompleteVariety


namespace IsCompleteVariety

/--
[lemma_16_12](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CompleteVarieties.lean)
-/
@[path]
lemma lemma_16_12
  {X : Type u}
  [TopologicalSpace X]
  [hX : IsCompleteVariety X]
  {Y : Type u}
  [TopologicalSpace Y]
  [IsVariety Y]
  {φ : X → Y}
-- given
  (hφ : Continuous φ)
  (hgraph : IsClosed {p : X × Y | p.2 = φ p.1}) :
-- imply
  IsClosedMap φ ∧ IsCompleteVariety (Set.range φ) := by
-- proof
  constructor
  ·
    intro Z hZ
    have hZuniv : IsClosed (Z ×ˢ (Set.univ : Set Y)) := hZ.prod isClosed_univ
    have hinter : IsClosed ({p : X × Y | p.2 = φ p.1} ∩ (Z ×ˢ Set.univ)) :=
      hgraph.inter hZuniv
    have hproj := hX.isClosedMap_snd Y _ hinter
    suffices h : φ '' Z = Prod.snd '' ({p : X × Y | p.2 = φ p.1} ∩ (Z ×ˢ Set.univ)) from
      h ▸ hproj
    ext y
    constructor
    · rintro ⟨x, hxZ, rfl⟩
      exact ⟨(x, φ x), ⟨rfl, hxZ, Set.mem_univ _⟩, rfl⟩
    · rintro ⟨⟨x, y'⟩, ⟨hy', hxZ, _⟩, rfl⟩
      exact ⟨x, hxZ, hy'.symm⟩
  ·
    exact {
      isVariety := TopologicalSpace.NoetherianSpace.range φ hφ
      isClosedMap_snd := by
        intro Z _inst _var S hS
        let ψ : X × Z → (Set.range φ) × Z := Prod.map (Set.rangeFactorization φ) id
        have hψ : Continuous ψ := (hφ.rangeFactorization).prodMap continuous_id
        have hpreimage : IsClosed (ψ ⁻¹' S) := hS.preimage hψ
        have hproj := hX.isClosedMap_snd Z _ hpreimage
        convert hproj using 1
        ext z
        constructor
        · rintro ⟨⟨⟨y, hy⟩, z'⟩, hS', rfl⟩
          obtain ⟨x, rfl⟩ := hy
          exact ⟨(x, z'), hS', rfl⟩
        · rintro ⟨⟨x, z'⟩, hS', rfl⟩
          exact ⟨(⟨φ x, x, rfl⟩, z'), hS', rfl⟩
    }

end IsCompleteVariety

namespace IsCompleteVariety

/--
[isCompleteVariety_of_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CompleteVarieties.lean)
-/
@[path]
lemma isCompleteVariety_of_isClosed
  {X : Type u}
  [TopologicalSpace X]
  [hX : IsCompleteVariety X]
  {V : Set X}
-- given
  (hV : IsClosed V) :
-- imply
  IsCompleteVariety V where isVariety :=
-- proof
  TopologicalSpace.NoetherianSpace.set V
    isClosedMap_snd := by
      intro Z _inst _noeth
      have h_eq : (Prod.snd : V × Z → Z) = (Prod.snd : X × Z → Z) ∘ Prod.map Subtype.val id := by
        ext ⟨v, z⟩; simp
      rw [h_eq]
      have h_incl : Topology.IsClosedEmbedding (Prod.map (Subtype.val : V → X) (id : Z → Z)) := by
        constructor
        · exact (Topology.IsClosedEmbedding.subtypeVal hV).isEmbedding.prodMap .id
        · rw [Set.range_prodMap, Subtype.range_val, Set.range_id]
          exact hV.prod isClosed_univ
      exact (hX.isClosedMap_snd Z).comp h_incl.isClosedMap
end IsCompleteVariety
open AlgebraicGeometry


/--
[complete_affine_variety_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CompleteVarieties.lean)
-/
@[path]
lemma complete_affine_variety_subsingleton
  {K : Type u}
  [Field K]
  {X : Scheme.{u}}
  {f : X ⟶ Spec (.of K)}
  [IsAffine X]
  [IsIntegral X]
  [IsProper f] :
-- imply
  Subsingleton X := by
-- proof
  have hfield : IsField Γ(X, ⊤) := isField_of_universallyClosed K f
  have hsub : Subsingleton (PrimeSpectrum Γ(X, ⊤)) := by
    rwa [PrimeSpectrum.subsingleton_iff_isField_of_isReduced]
  have : Subsingleton (Spec Γ(X, ⊤)) := hsub
  exact X.isoSpec.hom.homeomorph.toEquiv.subsingleton


-- created on 2026-10-23
