import Mathlib
import Lemma.Definitions.Def_ModularCurve_DRModelPackageLevel
import Lemma.Definitions.Def_ModularCurve_X0MqResolvedTable
import Lemma.Definitions.Def_AlgebraicCurve_RelCartier
import Lemma.Definitions.Def_ModularCurve_DRResolvedModelPackageLevel

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ModularCurve.IgusaScheme

namespace ModularCurve

attribute [local instance] DRModelPackageLevel.neZero_mul

namespace DRLevel

abbrev unifOn {O : Type} [CommRing O] {Y : Scheme.{0}} (toBase : Y ⟶ Spec (CommRingCat.of O)) (ϖ : O) (U : Y.affineOpens) : Γ(Y, U) :=
  (Y.presheaf.map (homOfLE le_top).op) (toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ))

theorem unifOn_natCast {O : Type} [CommRing O] {Y : Scheme.{0}} (toBase : Y ⟶ Spec (CommRingCat.of O)) (n : ℕ)
    (U : Y.affineOpens) : unifOn toBase (n : O) U = (n : Γ(Y, U)) := by
  simp [unifOn, map_natCast]

end DRLevel

open DRLevel

structure DRResolvedModelPackageLevelRam (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] (ρ : R q →+* O) (ϖ : O)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ) where

  Y : Scheme.{0}
  toBase : Y ⟶ Spec (CommRingCat.of O)
  toDR : Y ⟶ XO (N₀ := N₀) ρ
  toDR_over : toDR ≫ pullback.snd _ _ = toBase
  [toDR_proper : IsProper toDR]
  [isProper : IsProper toBase]
  [flat : Flat toBase]
  [isIntegral : IsIntegral Y]
  [isLocallyNoetherian : IsLocallyNoetherian Y]

  regular : ∀ y : Y, y ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) →
    IsRegularLocalRing (Y.presheaf.stalk y)
  stalk_dim_le_two : ∀ y : Y, y ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) →
    ringKrullDim (Y.presheaf.stalk y) ≤ 2

  toDR_iso_smoothLocus : IsIso (toDR ∣_ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρ)) ⁻¹ᵁ 𝔛.smoothLocus))
  toDR_iso_generic : IsIso (toDR ∣_ (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρ)) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)))

  node : Type
  [node_fintype : Fintype node]
  [node_deq : DecidableEq node]
  width : node → ℕ
  one_le_width : ∀ n, 1 ≤ width n

  nodeEquiv : node ≃ ↥(pullback (𝔛.comp κ (toκ.comp ρ) 0) (𝔛.comp κ (toκ.comp ρ) 1))
  comp : X0MqComponents width → Y.IdealSheafData
  comp_isInvertible : ∀ v, (comp v).IsInvertible
  comp_integral : ∀ v, IsIntegral (comp v).subscheme
  comp_support : ∀ v (y : Y), y ∈ (comp v).support →
    y ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)
  comp_prod : ∀ U : Y.affineOpens, (∏ v, comp v).ideal U = Ideal.span {DRLevel.unifOn toBase ϖ U}
  η : X0MqComponents width → Y
  η_not_mem : ∀ v, η v ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)
  η_stalk : ∀ v, ∃ (U : Y.affineOpens) (hU : η v ∈ (U : Y.Opens)),
    Ideal.map (Y.presheaf.germ (U : Y.Opens) (η v) hU).hom ((comp v).ideal U) =
        IsLocalRing.maximalIdeal (Y.presheaf.stalk (η v)) ∧
      ∀ w, w ≠ v → Ideal.map (Y.presheaf.germ (U : Y.Opens) (η v) hU).hom ((comp w).ideal U) = ⊤
  codim : ∀ y : Y, y ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) →
    ringKrullDim (Y.presheaf.stalk y) ≤ 1 → ∃ v, y = η v

  strict_iso : ∀ i : Fin 2,
    ∃ e : pullback ((comp (Sum.inl i)).subschemeι ≫ toBase) (Spec.map (CommRingCat.ofHom toκ)) ⟶ fibre0 (N₀ := N₀) (toκ.comp ρ),
      IsIso e ∧ e ≫ pullback.snd _ _ = pullback.snd _ _ ∧
        e ≫ 𝔛.comp κ (toκ.comp ρ) i ≫ bcMap ρ toκ = pullback.fst _ _ ≫ (comp (Sum.inl i)).subschemeι ≫ toDR

  exc_image : ∀ (n : node) (i : Fin (width n - 1)), ∀ y ∈ (comp (Sum.inr ⟨n, i⟩)).support,
    toDR.base y = (pullback.fst (𝔛.comp κ (toκ.comp ρ) 0) (𝔛.comp κ (toκ.comp ρ) 1) ≫ 𝔛.comp κ (toκ.comp ρ) 0 ≫
      bcMap ρ toκ).base (nodeEquiv n)

  edgePt : (n : node) → Fin (width n) → Y
  edgePt_injective : Function.Injective (fun e : Σ n, Fin (width n) => edgePt e.1 e.2)
  edgePt_mem : ∀ (n : node) (d : Fin (width n)),
    edgePt n d ∈ ((comp (DRResolvedModelPackageLevel.chainPos width n d)).support : Set Y) ∩
      ((comp (DRResolvedModelPackageLevel.chainPos width n (d + 1))).support : Set Y)
  edgePt_over : ∀ (n : node) (d : Fin (width n)),
    toDR.base (edgePt n d) = (pullback.fst (𝔛.comp κ (toκ.comp ρ) 0) (𝔛.comp κ (toκ.comp ρ) 1) ≫ 𝔛.comp κ (toκ.comp ρ) 0 ≫
      bcMap ρ toκ).base (nodeEquiv n)
  edgePt_exhaust : ∀ v w, v ≠ w → ∀ y ∈ ((comp v).support : Set Y) ∩ ((comp w).support : Set Y),
    ∃ (n : node) (d : Fin (width n)), y = edgePt n d ∧
      ((v = DRResolvedModelPackageLevel.chainPos width n d ∧ w = DRResolvedModelPackageLevel.chainPos width n (d + 1)) ∨
       (w = DRResolvedModelPackageLevel.chainPos width n d ∧ v = DRResolvedModelPackageLevel.chainPos width n (d + 1)))
  edgePt_transversal : ∀ (n : node) (d : Fin (width n)), ∃ (U : Y.affineOpens) (hU : edgePt n d ∈ (U : Y.Opens)),
    Ideal.map (Y.presheaf.germ (U : Y.Opens) (edgePt n d) hU).hom
        ((comp (DRResolvedModelPackageLevel.chainPos width n d)).ideal U ⊔
          (comp (DRResolvedModelPackageLevel.chainPos width n (d + 1))).ideal U) =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (edgePt n d))

  exc_rational : ∀ (n : node) (i : Fin (width n - 1)),
    ∃ (M : AlgebraicCurve.CurveModel κ (RatFunc κ))
      (e : M.C ⟶ pullback ((comp (Sum.inr ⟨n, i⟩)).subschemeι ≫ toBase) (Spec.map (CommRingCat.ofHom toκ))),
      IsIso e ∧ e ≫ pullback.snd _ _ = M.toBase

  smoothOffEdges : Y.Opens
  [smoothOffEdges_smooth : SmoothOfRelativeDimension 1 (smoothOffEdges.ι ≫ toBase)]
  mem_smoothOffEdges : ∀ y : Y, (∀ (n : node) (d : Fin (width n)), y ≠ edgePt n d) → y ∈ smoothOffEdges

attribute [instance] DRResolvedModelPackageLevelRam.toDR_proper DRResolvedModelPackageLevelRam.isProper DRResolvedModelPackageLevelRam.flat
  DRResolvedModelPackageLevelRam.isIntegral DRResolvedModelPackageLevelRam.isLocallyNoetherian DRResolvedModelPackageLevelRam.node_fintype
  DRResolvedModelPackageLevelRam.node_deq DRResolvedModelPackageLevelRam.smoothOffEdges_smooth

def DRResolvedModelPackageLevelRam.ofUnramified {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} {𝔛 : DRModelPackageLevel N₀ q hqN}
    {O : Type} [CommRing O] {ρ : R q →+* O} {κ : Type} [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ}
    (𝔜 : DRResolvedModelPackageLevel N₀ q 𝔛 O ρ κ toκ) : DRResolvedModelPackageLevelRam N₀ q 𝔛 O ρ ((q : ℕ) : O) κ toκ :=
  { 𝔜 with comp_prod := fun U => (𝔜.comp_prod U).trans (by rw [DRLevel.unifOn_natCast]) }

end ModularCurve

end
