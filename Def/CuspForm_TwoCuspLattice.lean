module

public import Mathlib
public import Def.CohCarrier_Inst
public import Def.CuspForm_HeckeOperatorFormsGammaH
public import Def.ModularForm_AtkinLehnerDatum
public import Def.FLTPrelim_Modularity

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm
open CongruenceSubgroup CohCarrier ZMod

namespace CuspForm

section HeckeRing

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

def heckeGenH (S : Set ℕ) (k : ℤ) :
    Gen M S → (CuspForm (GammaH M H) k →ₗ[ℂ] CuspForm (GammaH M H) k)
  | .T _ hℓ _ hℓM => heckeTLinH k hℓ hℓM
  | .U q _ _ => heckeULinH k q
  | .dia d => diamondLinH k d

variable (M H) in

def heckeRingH (k : ℤ) : Subring (CuspForm (GammaH M H) k →ₗ[ℂ] CuspForm (GammaH M H) k) :=
  Subring.closure (Set.range (heckeGenH (H := H) (∅ : Set ℕ) k))

end HeckeRing

section Lattice

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (p : ℕ) (A : Subring ℂ)

def twoCuspIntegralSet : Set (CuspForm (GammaH M H) k) :=
  {f | ∀ t ∈ heckeRingH M H k, ∀ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
    ModularFormClass.qCoeff (⇑(t f)) n ∈ A ∧
      ModularFormClass.qCoeff (ModularForm.alSlash W k ⇑(t f)) n ∈ A}

variable {M H k p A} in
variable {M H k p A} in

def twoCuspLattice : Submodule A (CuspForm (GammaH M H) k) :=
  Submodule.span A (twoCuspIntegralSet M H k p A)

variable {M H k p A} in

variable {M H k p A} in

def twoCuspEnd (t : heckeRingH M H k) : twoCuspLattice M H k p A →ₗ[A] twoCuspLattice M H k p A where
  toFun x := ⟨(t : CuspForm (GammaH M H) k →ₗ[ℂ] _) x, heckeRingH_apply_mem_twoCuspLattice t.2 x.2⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' a x := Subtype.ext (by
    simp only [Submodule.coe_smul, RingHom.id_apply, Subring.smul_def, LinearMap.map_smul])

end Lattice

section Reduction

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (p : ℕ) (A : Subring ℂ) (I : Ideal A)

def TwoCuspForms : Type :=
  twoCuspLattice M H k p A ⧸ (I • ⊤ : Submodule A (twoCuspLattice M H k p A))

variable {M H k p A} in

def twoCuspReduce : twoCuspLattice M H k p A →ₗ[A] TwoCuspForms M H k p A I :=
  (I • ⊤ : Submodule A (twoCuspLattice M H k p A)).mkQ

variable {M H k p A} in

def twoCuspEndModAux (t : heckeRingH M H k) : TwoCuspForms M H k p A I →ₗ[A] TwoCuspForms M H k p A I :=
  Submodule.mapQ (I • ⊤ : Submodule A (twoCuspLattice M H k p A)) (I • ⊤ : Submodule A (twoCuspLattice M H k p A))
    (twoCuspEnd t) (by
      rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top)

variable {M H k p A} in

def twoCuspEndMod (t : heckeRingH M H k) : TwoCuspForms M H k p A I →ₗ[A ⧸ I] TwoCuspForms M H k p A I :=
  LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective (twoCuspEndModAux I t)

variable {M H k p A} in

def twoCuspGenMod (S : Set ℕ) (g : Gen M S) : TwoCuspForms M H k p A I →ₗ[A ⧸ I] TwoCuspForms M H k p A I :=
  twoCuspEndMod I ⟨heckeGenH S k g, heckeGenH_mem_heckeRingH S k g⟩

variable {M H k p A} in

def twoCuspEigenspace (S : Set ℕ) (χ : Gen M S → A ⧸ I) : Submodule (A ⧸ I) (TwoCuspForms M H k p A I) where
  carrier := {ω | ∀ g : Gen M S, twoCuspGenMod I S g ω = χ g • ω}
  zero_mem' g := by rw [map_zero, smul_zero]
  add_mem' {x y} hx hy g := by rw [map_add, hx g, hy g, smul_add]
  smul_mem' c {x} hx g := by rw [LinearMap.map_smul, hx g, smul_comm]

end Reduction

end CuspForm

end
