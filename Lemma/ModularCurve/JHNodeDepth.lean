import Mathlib
import Def.ModularCurve_JHPlaceSpecialization
import Lemma.ModularCurve.ComponentGroup
import Def.ModularCurve_NodeDepth
import Lemma.AlgebraicCurve.SemistableCharts
import Notation.ModularCurve_JHNodeDepth

set_option autoImplicit false
set_option quotPrecheck false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

namespace ModularCurve
namespace JHPlaceSpecialization

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
variable (A : ValuationSubring (AlgebraicClosure ℚ))
variable [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]

open scoped ModularCurve_JHNodeDepth

variable {p M H hpM A}

namespace ProlongationDatum

variable {P : JHPlaceSpecialization p M H hpM A}
variable {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}

def nodeIntegers (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) : Subring FM where
  carrier := {f | f ∈ R.R₁.integers ∧ f ∈ R.R₂.integers ∧
    ∀ V : Place (AlgebraicClosure ℚ) FM, P.reduceFst α hα V = w → f ∈ V.toValuationSubring}
  zero_mem' := ⟨zero_mem _, zero_mem _, fun V _ => zero_mem _⟩
  one_mem' := ⟨one_mem _, one_mem _, fun V _ => one_mem _⟩
  add_mem' := by
    rintro f g ⟨hf₁, hf₂, hf⟩ ⟨hg₁, hg₂, hg⟩
    exact ⟨add_mem hf₁ hg₁, add_mem hf₂ hg₂, fun V hV => add_mem (hf V hV) (hg V hV)⟩
  neg_mem' := by
    rintro f ⟨hf₁, hf₂, hf⟩
    exact ⟨neg_mem hf₁, neg_mem hf₂, fun V hV => neg_mem (hf V hV)⟩
  mul_mem' := by
    rintro f g ⟨hf₁, hf₂, hf⟩ ⟨hg₁, hg₂, hg⟩
    exact ⟨mul_mem hf₁ hg₁, mul_mem hf₂ hg₂, fun V hV => mul_mem (hf V hV) (hg V hV)⟩

omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem mem_nodeIntegers_iff (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) (f : FM) :
    f ∈ R.nodeIntegers α hα w ↔ f ∈ R.R₁.integers ∧ f ∈ R.R₂.integers ∧
      ∀ V : Place (AlgebraicClosure ℚ) FM, P.reduceFst α hα V = w → f ∈ V.toValuationSubring :=
  Iff.rfl

omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem mem_toValuationSubring_of_mem_nodeIntegers (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    {w : Place κ Fb} {f : FM} (hf : f ∈ R.nodeIntegers α hα w)
    {V : Place (AlgebraicClosure ℚ) FM} (hV : P.reduceFst α hα V = w) :
    f ∈ V.toValuationSubring :=
  hf.2.2 V hV

omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in

theorem ord_nonneg_of_mem_nodeIntegers (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    {w : Place κ Fb} {f : FM} (hf : f ∈ R.nodeIntegers α hα w)
    {V : Place (AlgebraicClosure ℚ) FM} (hV : P.reduceFst α hα V = w) :
    0 ≤ V.ord f :=
  V.ord_nonneg_of_mem (hf.2.2 V hV)

omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem nodeIntegers_le_integersFst (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) : R.nodeIntegers α hα w ≤ R.R₁.integers.toSubring :=
  fun _ hf => hf.1

omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem nodeIntegers_le_integersSnd (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) : R.nodeIntegers α hα w ≤ R.R₂.integers.toSubring :=
  fun _ hf => hf.2.1

def nodeResidue₁ (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) : ↥(R.nodeIntegers α hα w) →+* Fb :=
  R.R₁.residue.comp (Subring.inclusion (R.nodeIntegers_le_integersFst α hα w))

def nodeResidue₂ (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) : ↥(R.nodeIntegers α hα w) →+* Fb :=
  R.R₂.residue.comp (Subring.inclusion (R.nodeIntegers_le_integersSnd α hα w))

omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem nodeResidue₁_apply (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) (f : ↥(R.nodeIntegers α hα w)) :
    R.nodeResidue₁ α hα w f = R.R₁.residue ⟨f, f.2.1⟩ := rfl

omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem nodeResidue₂_apply (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) (f : ↥(R.nodeIntegers α hα w)) :
    R.nodeResidue₂ α hα w f = R.R₂.residue ⟨f, f.2.2.1⟩ := rfl

omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem algebraMap_mem_nodeIntegers (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) (c : A) :
    algebraMap (AlgebraicClosure ℚ) FM (c : AlgebraicClosure ℚ) ∈ R.nodeIntegers α hα w :=
  ⟨(R.R₁.algebraMap_mem_iff (c : AlgebraicClosure ℚ)).mpr c.2, (R.R₂.algebraMap_mem_iff (c : AlgebraicClosure ℚ)).mpr c.2,
    fun V _ => V.algebraMap_mem' _⟩

def ValueIntegralityLaw (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) : Prop :=
  ∀ f : FM, f ∈ R.nodeIntegers α hα w →
    ∀ V : Place (AlgebraicClosure ℚ) FM, P.reduceFst α hα V = w → V.evalAt f ∈ A

end ProlongationDatum

def AnnulusDepthLaw (P : JHPlaceSpecialization p M H hpM A) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (s : Place κ Fb × Place κ Fb) (An : AlgebraicCurve.Annulus A FM)
    (depth : Place (AlgebraicClosure ℚ) FM → ℕ) : Prop :=
  ∀ V : Place (AlgebraicClosure ℚ) FM, P.reduceFst α hα V = s.1 →
    (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V = V) →
    A.valuation (V.evalAt An.param) = A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ depth V

def depthDiv (P : JHPlaceSpecialization p M H hpM A) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (depth : Place (AlgebraicClosure ℚ) FM → ℕ) (D : Divisor (AlgebraicClosure ℚ) FM) : Divisor κ Fb :=
  D.sum fun V n => Finsupp.single (P.reduceFst α hα V) (n * (depth V : ℤ))

def depthDual (P : JHPlaceSpecialization p M H hpM A) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (SS : Finset (Place κ Fb × Place κ Fb))
    (depth : Place (AlgebraicClosure ℚ) FM → ℕ) (D : Divisor (AlgebraicClosure ℚ) FM) :
    Module.Dual ℤ (characterLattice ↥SS) :=
  ∑ s : ↥SS, P.depthDiv α hα depth D (s : Place κ Fb × Place κ Fb).1 • crossingCoord s

def DepthCompLaw (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (SS : Finset (Place κ Fb × Place κ Fb))
    (e : ↥SS → ℕ) (depth : Place (AlgebraicClosure ℚ) FM → ℕ)
    (comp : ↥(JHPlaceSpecialization.inertiaInvariants M H A) →+ componentGroup e) : Prop :=
  ∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := FM)))
    (hH : Pic0.mk D ∈ JHPlaceSpecialization.inertiaInvariants M H A),
    (∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) FM).support,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ,
          arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V = V) ∧
        (P.IsStrictFst α β hα hβ δ V ∨ P.IsStrictSnd α β hα hβ δ V ∨ ∃ s ∈ SS, P.reduceFst α hα V = s.1)) →
    ∀ s₀ : ↥SS,
      comp ⟨Pic0.mk D, hH⟩ =
        componentGroupProj e
          (P.depthDual α hα SS depth (D : Divisor (AlgebraicClosure ℚ) FM) +
            Divisor.degree (P.sndDiv α β hα hβ δ (D : Divisor (AlgebraicClosure ℚ) FM)) •
              ((e s₀ : ℤ) • crossingCoord s₀))

end JHPlaceSpecialization
end ModularCurve

end
