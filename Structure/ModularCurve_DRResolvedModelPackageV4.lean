import Mathlib
import Structure.ModularCurve_DRModelPackage
import Def.ModularCurve_X0MqResolvedTable
import Def.AlgebraicCurve_RelCartier
import Instance.AlgebraicGeometry_RelativePicardFunctor
import Def.ModularCurve_DRResolvedModelPackageV4

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace ModularCurve


variable (p : ℕ) [Fact p.Prime]


structure DRResolvedModelPackage (𝔛 : DRModelPackage p) (O : Type) [CommRing O]
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ) where

  Y : Scheme.{0}

  toBase : Y ⟶ Spec (CommRingCat.of O)

  toDR : Y ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))
  toDR_over : toDR ≫ pullback.snd _ _ = toBase
  [toDR_proper : IsProper toDR]
  [isProper : IsProper toBase]
  [flat : Flat toBase]
  [isIntegral : IsIntegral Y]
  [isLocallyNoetherian : IsLocallyNoetherian Y]

  regular : ∀ y : Y, y ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) →
    IsRegularLocalRing (Y.presheaf.stalk y)

  stalk_dim_le_two : ∀ y : Y, y ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) →
    ringKrullDim (Y.presheaf.stalk y) ≤ 2

  toDR_iso_smoothLocus : IsIso (toDR ∣_ (pullback.fst (DRModel.toBase p) _ ⁻¹ᵁ 𝔛.smoothLocus))

  toDR_iso_generic : IsIso (toDR ∣_ (pullback.snd (DRModel.toBase p) _ ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)))

  node : Type
  [node_fintype : Fintype node]
  [node_deq : DecidableEq node]

  width : node → ℕ
  one_le_width : ∀ n, 1 ≤ width n

  nodeEquiv : node ≃ ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ))

  comp : X0MqComponents width → Y.IdealSheafData

  comp_isInvertible : ∀ v, (comp v).IsInvertible

  comp_integral : ∀ v, IsIntegral (comp v).subscheme

  comp_support : ∀ v (y : Y), y ∈ (comp v).support →
    y ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)

  comp_prod : ∀ U : Y.affineOpens, (∏ v, comp v).ideal U = Ideal.span {((p : ℕ) : Γ(Y, U))}

  η : X0MqComponents width → Y
  η_not_mem : ∀ v, η v ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)

  η_stalk : ∀ v, ∃ (U : Y.affineOpens) (hU : η v ∈ (U : Y.Opens)),
    Ideal.map (Y.presheaf.germ (U : Y.Opens) (η v) hU).hom ((comp v).ideal U) =
        IsLocalRing.maximalIdeal (Y.presheaf.stalk (η v)) ∧
      ∀ w, w ≠ v → Ideal.map (Y.presheaf.germ (U : Y.Opens) (η v) hU).hom ((comp w).ideal U) = ⊤

  codim : ∀ y : Y, y ∉ toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) →
    ringKrullDim (Y.presheaf.stalk y) ≤ 1 → ∃ v, y = η v

  strict_iso_inf : ∃ e : pullback ((comp (Sum.inl 0)).subschemeι ≫ toBase) (Spec.map (CommRingCat.ofHom toκ)) ⟶ (𝔛.ratModel κ).C,
    IsIso e ∧ e ≫ (𝔛.ratModel κ).toBase = pullback.snd _ _ ∧
      e ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ = pullback.fst _ _ ≫ (comp (Sum.inl 0)).subschemeι ≫ toDR
  strict_iso_zero : ∃ e : pullback ((comp (Sum.inl 1)).subschemeι ≫ toBase) (Spec.map (CommRingCat.ofHom toκ)) ⟶ (𝔛.ratModel κ).C,
    IsIso e ∧ e ≫ (𝔛.ratModel κ).toBase = pullback.snd _ _ ∧
      e ≫ 𝔛.compZero κ ≫ DRModel.baseChangeMap toκ = pullback.fst _ _ ≫ (comp (Sum.inl 1)).subschemeι ≫ toDR

  exc_image : ∀ (n : node) (i : Fin (width n - 1)), ∀ y ∈ (comp (Sum.inr ⟨n, i⟩)).support,
    toDR.base y = (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (nodeEquiv n)

  edgePt : (n : node) → Fin (width n) → Y
  edgePt_injective : Function.Injective (fun e : Σ n, Fin (width n) => edgePt e.1 e.2)

  edgePt_mem : ∀ (n : node) (d : Fin (width n)),
    edgePt n d ∈ ((comp (DRResolvedModelPackage.chainPos width n d)).support : Set Y) ∩ ((comp (DRResolvedModelPackage.chainPos width n (d + 1))).support : Set Y)

  edgePt_over : ∀ (n : node) (d : Fin (width n)),
    toDR.base (edgePt n d) = (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (nodeEquiv n)

  edgePt_exhaust : ∀ v w, v ≠ w → ∀ y ∈ ((comp v).support : Set Y) ∩ ((comp w).support : Set Y),
    ∃ (n : node) (d : Fin (width n)), y = edgePt n d ∧
      ((v = DRResolvedModelPackage.chainPos width n d ∧ w = DRResolvedModelPackage.chainPos width n (d + 1)) ∨
       (w = DRResolvedModelPackage.chainPos width n d ∧ v = DRResolvedModelPackage.chainPos width n (d + 1)))

  edgePt_transversal : ∀ (n : node) (d : Fin (width n)), ∃ (U : Y.affineOpens) (hU : edgePt n d ∈ (U : Y.Opens)),
    Ideal.map (Y.presheaf.germ (U : Y.Opens) (edgePt n d) hU).hom
        ((comp (DRResolvedModelPackage.chainPos width n d)).ideal U ⊔ (comp (DRResolvedModelPackage.chainPos width n (d + 1))).ideal U) =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (edgePt n d))

  exc_rational : ∀ (n : node) (i : Fin (width n - 1)),
    ∃ (M : AlgebraicCurve.CurveModel κ (RatFunc κ))
      (e : M.C ⟶ pullback ((comp (Sum.inr ⟨n, i⟩)).subschemeι ≫ toBase) (Spec.map (CommRingCat.ofHom toκ))),
      IsIso e ∧ e ≫ pullback.snd _ _ = M.toBase

  smoothOffEdges : Y.Opens
  [smoothOffEdges_smooth : SmoothOfRelativeDimension 1 (smoothOffEdges.ι ≫ toBase)]

  mem_smoothOffEdges : ∀ y : Y, (∀ (n : node) (d : Fin (width n)), y ≠ edgePt n d) → y ∈ smoothOffEdges

end ModularCurve

end
