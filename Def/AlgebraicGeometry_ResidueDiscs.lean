module

public import Theorem.Scheme.RegularProlongation
public import Def.AlgebraicCurve_SemistableChartsComap

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Scheme.RegularProlongation

open IsLocalRing
open scoped Pointwise

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

section ResAut

variable (R : RegularProlongation A F Fbar) (τ : F ≃ₐ[L] F) (hτ : ∀ f : F, τ f ∈ R.integers ↔ f ∈ R.integers)

def integersEquiv : R.integers ≃+* R.integers where
  toFun x := ⟨τ x, (hτ x).mpr x.2⟩
  invFun y := ⟨τ.symm y, (hτ (τ.symm y)).mp (by rw [AlgEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (τ.symm_apply_apply x)
  right_inv y := Subtype.ext (τ.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul τ (x : F) (y : F))
  map_add' x y := Subtype.ext (map_add τ (x : F) (y : F))

def quotEquiv : (R.integers ⧸ RingHom.ker R.residue) ≃+* (R.integers ⧸ RingHom.ker R.residue) :=
  Ideal.quotientEquiv (RingHom.ker R.residue) (RingHom.ker R.residue) (R.integersEquiv τ hτ) (by
    apply le_antisymm
    · intro x hx
      have : x = R.integersEquiv τ hτ ((R.integersEquiv τ hτ).symm x) := ((R.integersEquiv τ hτ).apply_symm_apply x).symm
      rw [this]
      exact Ideal.mem_map_of_mem _ ((R.mem_ker_residue_iff_of_equiv τ hτ _).mp (by rw [← this]; exact hx))
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      exact (R.mem_ker_residue_iff_of_equiv τ hτ x).mpr hx)

def residueEquiv : (R.integers ⧸ RingHom.ker R.residue) ≃+* Fbar :=
  RingHom.quotientKerEquivOfSurjective R.residue_surjective

def resAutRingEquiv : Fbar ≃+* Fbar :=
  (R.residueEquiv.symm.trans (R.quotEquiv τ hτ)).trans R.residueEquiv

def resAut : Fbar ≃ₐ[ResidueField A] Fbar :=
  AlgEquiv.ofRingEquiv (f := R.resAutRingEquiv τ hτ) (by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    rw [← R.residue_algebraMap a, resAutRingEquiv_residue]
    congr 1
    apply Subtype.ext
    simp only [coe_integersEquiv]
    exact τ.commutes (a : L))

end ResAut

section Disc

variable (R : RegularProlongation A F Fbar)

def IsDiscCoord (Q : Place (ResidueField A) Fbar) (D : Set (Place L F)) (z : F) : Prop :=
  (∀ P ∈ D, P.IsRational ∧ z ∈ P.toValuationSubring ∧ A.valuation (P.evalAt z) < 1) ∧
  ∃ hz : z ∈ R.integers,
    Q.ord (R.residue ⟨z, hz⟩) = 1 ∧
    (∀ c : L, A.valuation c < 1 → ∃! P, P ∈ D ∧ P.evalAt z = c) ∧
    (∀ P ∈ D, P.ord (z - algebraMap L F (P.evalAt z)) = 1) ∧
    (∀ f : F, f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
      ∃ c : L, c ≠ 0 ∧ ∀ P ∈ D, A.valuation (P.evalAt f) = A.valuation c)

def PointwiseOn (Q : Place (ResidueField A) Fbar) (D : Set (Place L F)) : Prop :=
  ∀ P ∈ D, P.IsRational → ∀ (f : F) (hf : f ∈ R.integers),
    (∀ w ∈ D, f ∈ w.toValuationSubring) →
      ∃ (hm : (R.residue ⟨f, hf⟩ : Fbar) ∈ Q.toValuationSubring) (h : P.evalAt f ∈ A),
        algebraMap (ResidueField A) Q.ResidueField (IsLocalRing.residue A ⟨P.evalAt f, h⟩)
          = IsLocalRing.residue Q.toValuationSubring ⟨R.residue ⟨f, hf⟩, hm⟩

def DegreeOn (Q : Place (ResidueField A) Fbar) (D : Set (Place L F)) : Prop :=
  ∀ f : R.integers, R.residue f ≠ 0 → ∀ D' : Divisor L F,
    (∀ P ∈ D, D' P = P.ord (f : F)) → (∀ P, P ∉ D → D' P = 0) →
      D'.sum (fun _ n => n) = Q.ord (R.residue f)

def IsResidueDisc (Q : Place (ResidueField A) Fbar) (D : Set (Place L F)) (z : F) : Prop :=
  R.IsDiscCoord Q D z ∧ R.PointwiseOn Q D ∧ R.DegreeOn Q D

def IsDiscFibre (Q : Place (ResidueField A) Fbar) : Prop :=
  ∃ (D : Set (Place L F)) (z : F), R.IsResidueDisc Q D z

def InDiscFibre (Q : Place (ResidueField A) Fbar) (P : Place L F) : Prop :=
  ∃ (D : Set (Place L F)) (z : F), R.IsResidueDisc Q D z ∧ P ∈ D

def DiscFamily (N : Finset (Place (ResidueField A) Fbar))
    (disc : Place (ResidueField A) Fbar → Set (Place L F)) (coord : Place (ResidueField A) Fbar → F) : Prop :=
  (∀ Q, Q ∉ N → R.IsResidueDisc Q (disc Q) (coord Q)) ∧
  (∀ Q Q', Q ∉ N → Q' ∉ N → ∀ P, P ∈ disc Q → P ∈ disc Q' → Q = Q')

variable (τ : F ≃ₐ[L] F)

def smulDisc (D : Set (Place L F)) : Set (Place L F) := {P | τ⁻¹ • P ∈ D}

omit [Algebra (ResidueField A) Fbar] in
variable (hτ : ∀ f : F, τ f ∈ R.integers ↔ f ∈ R.integers)

include hτ in
end Disc

end Scheme.RegularProlongation

end
