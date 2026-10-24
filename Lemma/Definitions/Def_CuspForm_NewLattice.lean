import Lemma.Definitions.Def_CuspForm_HeckeAlgebra
import Lemma.Definitions.Def_CuspForm_IntegralStructure
import Lemma.Definitions.Def_CuspForm_LevelLoweringTrace
import Lemma.Definitions.Def_CuspForm_AtkinLehnerOperator

set_option autoImplicit false

noncomputable section

namespace CuspForm

open ModularForm

variable {M q : ℕ} [NeZero M] (A : AtkinLehnerDatum M q) (hq : q.Prime)

def newLattice : Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 M) 2) where
  carrier := {f | ∀ t ∈ heckeAlgebra M 2 {ℓ | ℓ ∣ M},
    t f ∈ intLattice M 2 ∧ traceLin A hq (t f) = 0 ∧ traceLin A hq (atkinLehnerLin A 2 (t f)) = 0}
  zero_mem' t _ := by
    rw [map_zero]
    exact ⟨Submodule.zero_mem _, by rw [map_zero], by rw [map_zero, map_zero]⟩
  add_mem' {f g} hf hg t ht := by
    obtain ⟨hf₁, hf₂, hf₃⟩ := hf t ht
    obtain ⟨hg₁, hg₂, hg₃⟩ := hg t ht
    rw [map_add]
    exact ⟨Submodule.add_mem _ hf₁ hg₁, by rw [map_add, hf₂, hg₂, add_zero],
      by rw [map_add, map_add, hf₃, hg₃, add_zero]⟩
  smul_mem' c {f} hf t ht := by
    obtain ⟨hf₁, hf₂, hf₃⟩ := hf t ht
    rw [map_zsmul]
    exact ⟨Submodule.smul_mem _ c hf₁, by rw [map_zsmul, hf₂, smul_zero],
      by rw [map_zsmul, map_zsmul, hf₃, smul_zero]⟩

variable {A hq}

theorem mem_newLattice_iff {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2} :
    f ∈ newLattice A hq ↔ ∀ t ∈ heckeAlgebra M 2 {ℓ | ℓ ∣ M},
      t f ∈ intLattice M 2 ∧ traceLin A hq (t f) = 0 ∧ traceLin A hq (atkinLehnerLin A 2 (t f)) = 0 :=
  Iff.rfl

theorem apply_mem_newLattice {t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)}
    (ht : t ∈ heckeAlgebra M 2 {ℓ | ℓ ∣ M}) {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hf : f ∈ newLattice A hq) : t f ∈ newLattice A hq :=
  fun s hs => hf (s * t) (Subalgebra.mul_mem _ hs ht)

variable (A hq) in

def newLatticeEnd : heckeAlgebra M 2 {ℓ | ℓ ∣ M} →+* Module.End ℤ (newLattice A hq) where
  toFun t := ((t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)).restrictScalars ℤ).restrict
    fun _ hf => apply_mem_newLattice t.2 hf
  map_one' := LinearMap.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearMap.ext fun _ => Subtype.ext rfl
  map_zero' := LinearMap.ext fun _ => Subtype.ext rfl
  map_add' _ _ := LinearMap.ext fun _ => Subtype.ext rfl

instance instSMulHeckeAlgebraNewLattice : SMul (heckeAlgebra M 2 {ℓ | ℓ ∣ M}) (newLattice A hq) :=
  ⟨fun t a => newLatticeEnd A hq t a⟩

instance instModuleHeckeAlgebraNewLattice : Module (heckeAlgebra M 2 {ℓ | ℓ ∣ M}) (newLattice A hq) :=
  Module.compHom (newLattice A hq) (newLatticeEnd A hq)

theorem newLattice_coe_smul (t : heckeAlgebra M 2 {ℓ | ℓ ∣ M}) (a : newLattice A hq) :
    ((t • a : newLattice A hq) : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
      = (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) a :=
  rfl

variable (A hq) in

def pNewLattice (p : ℕ) : Submodule (heckeAlgebra M 2 {ℓ | ℓ ∣ M}) (newLattice A hq) where
  carrier := {a | ∃ b : newLattice A hq, a = (p : heckeAlgebra M 2 {ℓ | ℓ ∣ M}) • b}
  zero_mem' := ⟨0, (smul_zero _).symm⟩
  add_mem' := by
    rintro _ _ ⟨b, rfl⟩ ⟨c, rfl⟩
    exact ⟨b + c, (smul_add _ _ _).symm⟩
  smul_mem' := by
    rintro t _ ⟨b, rfl⟩
    exact ⟨t • b, by rw [smul_smul, smul_smul, mul_comm]⟩

theorem mem_pNewLattice_iff (p : ℕ) {a : newLattice A hq} :
    a ∈ pNewLattice A hq p ↔ ∃ b : newLattice A hq, a = (p : heckeAlgebra M 2 {ℓ | ℓ ∣ M}) • b :=
  Iff.rfl

variable (A hq) in

abbrev newLatticeRed (p : ℕ) : Type :=
  newLattice A hq ⧸ pNewLattice A hq p

instance instAddCommGroupNewLatticeRed (p : ℕ) : AddCommGroup (newLatticeRed A hq p) :=
  Submodule.Quotient.addCommGroup _

instance instModuleHeckeAlgebraNewLatticeRed (p : ℕ) :
    Module (heckeAlgebra M 2 {ℓ | ℓ ∣ M}) (newLatticeRed A hq p) :=
  Submodule.Quotient.module _

instance instSMulHeckeAlgebraNewLatticeRed (p : ℕ) :
    SMul (heckeAlgebra M 2 {ℓ | ℓ ∣ M}) (newLatticeRed A hq p) :=
  (instModuleHeckeAlgebraNewLatticeRed p).toDistribMulAction.toMulAction.toSMul

instance instMulActionHeckeAlgebraNewLatticeRed (p : ℕ) :
    MulAction (heckeAlgebra M 2 {ℓ | ℓ ∣ M}) (newLatticeRed A hq p) :=
  (instModuleHeckeAlgebraNewLatticeRed p).toDistribMulAction.toMulAction

instance instDistribMulActionHeckeAlgebraNewLatticeRed (p : ℕ) :
    DistribMulAction (heckeAlgebra M 2 {ℓ | ℓ ∣ M}) (newLatticeRed A hq p) :=
  (instModuleHeckeAlgebraNewLatticeRed p).toDistribMulAction

instance instSMulWithZeroHeckeAlgebraNewLatticeRed (p : ℕ) :
    SMulWithZero (heckeAlgebra M 2 {ℓ | ℓ ∣ M}) (newLatticeRed A hq p) :=
  (instModuleHeckeAlgebraNewLatticeRed p).toMulActionWithZero.toSMulWithZero

instance instMulActionWithZeroHeckeAlgebraNewLatticeRed (p : ℕ) :
    MulActionWithZero (heckeAlgebra M 2 {ℓ | ℓ ∣ M}) (newLatticeRed A hq p) :=
  (instModuleHeckeAlgebraNewLatticeRed p).toMulActionWithZero

variable (A hq) in

def newLatticeRedMk (p : ℕ) :
    newLattice A hq →ₗ[heckeAlgebra M 2 {ℓ | ℓ ∣ M}] newLatticeRed A hq p :=
  Submodule.mkQ _

theorem newLatticeRedMk_surjective (p : ℕ) : Function.Surjective (newLatticeRedMk A hq p) :=
  Submodule.mkQ_surjective _

theorem natCast_smul_newLatticeRed (p : ℕ) (x : newLatticeRed A hq p) :
    (p : heckeAlgebra M 2 {ℓ | ℓ ∣ M}) • x = 0 := by
  obtain ⟨a, rfl⟩ := newLatticeRedMk_surjective p x
  rw [← LinearMap.map_smul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, rfl⟩

variable (A hq) in

def newLatticeIncl : newLattice A hq →+ CuspForm (CongruenceSubgroup.Gamma0 M) 2 :=
  (newLattice A hq).subtype.toAddMonoidHom

theorem newLatticeIncl_apply (a : newLattice A hq) :
    newLatticeIncl A hq a = (a : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :=
  rfl

theorem newLatticeIncl_injective : Function.Injective (newLatticeIncl A hq) :=
  Subtype.val_injective

theorem newLatticeIncl_smul (t : heckeAlgebra M 2 {ℓ | ℓ ∣ M}) (a : newLattice A hq) :
    newLatticeIncl A hq (t • a)
      = (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) (newLatticeIncl A hq a) :=
  rfl

theorem newLatticeIncl_mem_intLattice (a : newLattice A hq) : newLatticeIncl A hq a ∈ intLattice M 2 :=
  (a.2 1 (Subalgebra.one_mem _)).1

theorem newLatticeIncl_mem (a : newLattice A hq) :
    newLatticeIncl A hq a ∈
      LinearMap.ker (traceLin A hq) ⊓ LinearMap.ker ((traceLin A hq) ∘ₗ (atkinLehnerLin A 2)) :=
  ⟨(a.2 1 (Subalgebra.one_mem _)).2.1, (a.2 1 (Subalgebra.one_mem _)).2.2⟩

end CuspForm

end
