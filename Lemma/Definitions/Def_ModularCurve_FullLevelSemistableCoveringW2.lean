import Lemma.Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Lemma.Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Lemma.Definitions.Def_AlgebraicCurve_ConstantReduction
import Lemma.Definitions.Def_DrinfeldCurve_FunctionField
import Lemma.Definitions.Def_GaloisRep_TameCharacter
import Lemma.Definitions.Def_FLTPrelim_Ramification
import Lemma.Definitions.Def_ModularCurve_ArithmeticGalois

set_option autoImplicit false

noncomputable section

namespace ModularCurve.FullLevel.SemistableCovering

open AlgebraicCurve IsLocalRing DrinfeldCurve CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}

def InducesOnChart {Fbar : Type} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A (fieldBar q M') Fbar) (g : SemilinearAut (AlgebraicClosure ℚ) (fieldBar q M'))
    (φ : Fbar ≃+* Fbar) : Prop :=
  ∃ hst : ∀ f : fieldBar q M', f ∈ C.integers ↔ g • f ∈ C.integers,
    ∀ (f : fieldBar q M') (hf : f ∈ C.integers), C.residue ⟨g • f, (hst f).mp hf⟩ = φ (C.residue ⟨f, hf⟩)

variable (𝒞 : SemistableCovering q M' A W)

abbrev _root_.DrinfeldCurve.quotField (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ] [Algebra (GaloisField q 2) κ]
    [IsDomain (CoordRing q κ)] (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2))) :
    IntermediateField κ (drinfeldFunctionField q κ) :=
  IntermediateField.fixedField (Subgroup.closure (Set.range fun ζ : ↥C =>
    hFunctionFieldAction q κ ⟨(1, ((ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : (GaloisField q 2)ˣ)),
      one_mem_hSubgroup_of_mem q ζ⟩))

def DrinfeldClause [Algebra (GaloisField q 2) (ResidueField A)] [IsDomain (CoordRing q (ResidueField A))]
    (π : AlgebraicClosure ℚ) (ι : GaloisField q 2 →+* ResidueField A)
    (η : ℕ) (ζ : Idx q) (s : ↥W) : Prop :=
  ∃ (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
    (e : 𝒞.FSS s ≃ₐ[ResidueField A] ↥(DrinfeldCurve.quotField q (ResidueField A) C)),

    (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (∃ φ : 𝒞.FSS s ≃+* 𝒞.FSS s, InducesOnChart (𝒞.CSS s) (SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ⁻¹)) φ) ∧
      ∀ φ : 𝒞.FSS s ≃+* 𝒞.FSS s,
        InducesOnChart (𝒞.CSS s) (SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ⁻¹)) φ →
        ∀ hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ hSubgroup q,
          ∀ x : 𝒞.FSS s, ((e (φ x) : ↥(DrinfeldCurve.quotField q (ResidueField A) C)) : drinfeldFunctionField q (ResidueField A)) =
            hFunctionFieldAction q (ResidueField A) ⟨_, hmem⟩
              ((e x : ↥(DrinfeldCurve.quotField q (ResidueField A) C)) : drinfeldFunctionField q (ResidueField A))) ∧

    (∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ, ι (α : GaloisField q 2) = A.tameCharacter π τ →
      (∃ φ : 𝒞.FSS s ≃+* 𝒞.FSS s, InducesOnChart (𝒞.CSS s)
          (ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ) φ) ∧
      ∀ φ : 𝒞.FSS s ≃+* 𝒞.FSS s,
        InducesOnChart (𝒞.CSS s)
          (ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ) φ →
        ∀ (d : (ZMod q)ˣ), algebraMap (ZMod q) (GaloisField q 2) (d : ZMod q) = (α : GaloisField q 2) ^ (q + 1) →
          ∀ hmem : (diagOneElem q (d ^ η)⁻¹, α ^ η) ∈ hSubgroup q,
            ∀ x : 𝒞.FSS s, ((e (φ x) : ↥(DrinfeldCurve.quotField q (ResidueField A) C)) : drinfeldFunctionField q (ResidueField A)) =
              hFunctionFieldAction q (ResidueField A) ⟨_, hmem⟩
                ((e x : ↥(DrinfeldCurve.quotField q (ResidueField A) C)) : drinfeldFunctionField q (ResidueField A)))

def IgusaUnipotentClause (ζ : Idx q) : Prop :=
  ∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → (∃ t : ZMod q, redQ q γ = CuspidalType.unipotent q t) →
    InducesOnChart (𝒞.CIg (lineInfty q)) (SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ⁻¹)) (RingEquiv.refl _)

def LevelPinClauses (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M')) : Prop :=

  (∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
    (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
    (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
      ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ (𝒞.CSS s).integers,
        (𝒞.CSS s).residue ⟨_, hC⟩ = algebraMap (ResidueField A) (𝒞.FSS s)
          ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩))) ∧
  (∀ ℓ : CuspidalType.ProjLine q,
    ∃ j : modularFunctionFieldC (ResidueField A) M' →+* 𝒞.FIg ℓ,
      (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ (𝒞.CIg ℓ).integers,
          (𝒞.CIg ℓ).residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
      ∀ (s : ↥W) (g : modularFunctionFieldC (ResidueField A) M'),
        g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
          j g ∈ (𝒞.xs ℓ s).toValuationSubring)

def InertiaClause (π : AlgebraicClosure ℚ) : Prop :=
  ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
    let g := ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ
    (∀ ℓ, InducesOnChart (𝒞.CIg ℓ) g (RingEquiv.refl _) ∧
      (∀ P, (𝒞.CIg ℓ).placeMap (g • P) = (𝒞.CIg ℓ).placeMap P) ∧ (∀ P, P ∈ (𝒞.CIg ℓ).dom ↔ g • P ∈ (𝒞.CIg ℓ).dom)) ∧
    (∀ s, InducesOnChart (𝒞.CSS s) g (RingEquiv.refl _) ∧
      (∀ P, (𝒞.CSS s).placeMap (g • P) = (𝒞.CSS s).placeMap P) ∧ (∀ P, P ∈ (𝒞.CSS s).dom ↔ g • P ∈ (𝒞.CSS s).dom)) ∧
    (∀ ℓ s, (∀ P, P ∈ (𝒞.An ℓ s).dom ↔ g • P ∈ (𝒞.An ℓ s).dom) ∧
      g • (𝒞.An ℓ s).param = (𝒞.An ℓ s).param ∧ g • (𝒞.An' ℓ s).param = (𝒞.An' ℓ s).param)

def WidthClause (π : A) : Prop :=
  ∀ ℓ s, ∃ w : ℕ, 1 ≤ w ∧ ∃ u : Aˣ, (𝒞.An ℓ s).modulus = u * π ^ w

def W2Clauses [Algebra (GaloisField q 2) (ResidueField A)] [IsDomain (CoordRing q (ResidueField A))]
    (π : AlgebraicClosure ℚ) (ι : GaloisField q 2 →+* ResidueField A) (η : ℕ) : Prop :=
  (∀ (ζ : Idx q) (s : ↥W), 𝒞.DrinfeldClause π ι η ζ s) ∧ ∀ ζ : Idx q, 𝒞.IgusaUnipotentClause ζ

end ModularCurve.FullLevel.SemistableCovering

end
