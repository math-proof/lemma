import Structure.ModularCurve_ShimuraSubgroup
import Structure.ModularCurve_ShimuraCovering
import Abbrev.ModularCurve_ShimuraCovering

set_option autoImplicit false

noncomputable section

open IntermediateField AlgebraicCurve

namespace ModularCurve

section Supply

variable (L : Type*) [Field L] [Algebra ℚ L]


theorem coe_inclusionBar {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁)
    (x : laurentBaseChange L F₀) :
    (inclusionBar L h x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

theorem ramificationIndexAlong_inclusionBar_refl (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (w : Place L (laurentBaseChange L F₀)) :
    Place.ramificationIndexAlong (inclusionBar L (le_refl F₀)) w = 1 := by
  classical
  unfold Place.ramificationIndexAlong Place.ramificationIndex
  have hid : ∀ f : laurentBaseChange L F₀, inclusionBar L (le_refl F₀) f = f :=
    fun f => Subtype.ext (coe_inclusionBar L (le_refl F₀) f)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have h1 : (1 : ℕ) ∈ {n : ℕ | 0 < n ∧ ∃ f : laurentBaseChange L F₀, f ≠ 0 ∧
      w.ord (algebraMap (laurentBaseChange L F₀) (laurentBaseChange L F₀) f) = n} := by
    refine ⟨Nat.one_pos, (π : laurentBaseChange L F₀), ?_, ?_⟩
    · simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
    · show w.ord (inclusionBar L (le_refl F₀) π) = 1
      rw [hid, w.ord_coe_irreducible hπ]
  refine le_antisymm (Nat.sInf_le h1) ?_
  exact le_csInf ⟨1, h1⟩ fun n hn => hn.1

end Supply

section Carrier

variable (p : ℕ) [Fact p.Prime]


end Carrier

namespace ShimuraCoveringData

variable {p : ℕ} [Fact p.Prime] (D : ShimuraCoveringData p)


def coverHom : modularFunctionFieldBar p →ₐ[AlgebraicClosure ℚ] D.fieldBar :=
  inclusionBar (AlgebraicClosure ℚ) D.base_le

@[simp]
theorem coe_coverHom (x : modularFunctionFieldBar p) :
    (D.coverHom x : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ)) :=
  coe_inclusionBar _ _ x

def KernelInputs : Prop :=
  ∃ (hint : D.coverHom.toRingHom.IsIntegral)
    (_ : HasPrincipalDivisors (AlgebraicClosure ℚ) D.fieldBar),
    FundamentalIdentityAlong (AlgebraicClosure ℚ) D.coverHom hint

open Classical in

def kernel : AddSubgroup (JZero p) :=
  if h : D.KernelInputs then
    letI := algebraAlong D.coverHom
    haveI := isScalarTower_along D.coverHom
    haveI := isIntegral_along D.coverHom h.1
    haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) D.fieldBar := h.2.1
    haveI : FundamentalIdentity (AlgebraicClosure ℚ) (modularFunctionFieldBar p) D.fieldBar :=
      h.2.2
    (Pic0.pullbackHom (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p) D.fieldBar).ker
  else ⊥

theorem kernel_of_not (h : ¬ D.KernelInputs) : D.kernel = ⊥ := by
  rw [kernel, dif_neg h]

end ShimuraCoveringData

end ModularCurve

end
