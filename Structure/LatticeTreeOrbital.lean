import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Basic.Complex.Basic

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree

section Helpers

variable {α : Type*} [CommRing α]


end Helpers

variable (R : Type*) [CommRing R]
variable (K : Type*) [Field K] [Algebra R K]

def stdLattice : Submodule R (Fin 2 → K) where
  carrier := {v | ∀ i, IsLocalization.IsInteger R (v i)}
  add_mem' := fun hv hw i => IsLocalization.isInteger_add (hv i) (hw i)
  zero_mem' := fun _ => IsLocalization.isInteger_zero
  smul_mem' := fun r v hv i => by
    rw [Pi.smul_apply]
    exact IsLocalization.isInteger_smul (hv i)

theorem mem_stdLattice {v : Fin 2 → K} :
    v ∈ stdLattice R K ↔ ∀ i, IsLocalization.IsInteger R (v i) := Iff.rfl


variable {R K}

def mulVecLinR (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    (Fin 2 → K) →ₗ[R] (Fin 2 → K) where
  toFun v := (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v
  map_add' v w := Matrix.mulVec_add _ v w
  map_smul' r v := by
    rw [RingHom.id_apply]
    exact Matrix.mulVec_smul _ r v

@[simp] theorem mulVecLinR_apply (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Fin 2 → K) :
    mulVecLinR (R := R) g v = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v := rfl

def latticeMap (g : Matrix.GeneralLinearGroup (Fin 2) K) (L : Submodule R (Fin 2 → K)) :
    Submodule R (Fin 2 → K) :=
  L.map (mulVecLinR g)


theorem mulVecLinR_mul (g h : Matrix.GeneralLinearGroup (Fin 2) K) :
    mulVecLinR (R := R) (g * h) = (mulVecLinR g).comp (mulVecLinR h) :=
  LinearMap.ext fun v => by
    rw [LinearMap.comp_apply, mulVecLinR_apply, mulVecLinR_apply, mulVecLinR_apply,
      Matrix.mulVec_mulVec, Units.val_mul]

theorem latticeMap_one (L : Submodule R (Fin 2 → K)) : latticeMap 1 L = L := by
  have h : ∀ v : Fin 2 → K, mulVecLinR (R := R) 1 v = v := fun v => by
    rw [mulVecLinR_apply, Units.val_one, Matrix.one_mulVec]
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [show mulVecLinR (R := R) 1 w = w from h w]
    exact hw
  · intro hv
    exact ⟨v, hv, h v⟩

theorem latticeMap_mul (g h : Matrix.GeneralLinearGroup (Fin 2) K)
    (L : Submodule R (Fin 2 → K)) :
    latticeMap (g * h) L = latticeMap g (latticeMap h L) := by
  unfold latticeMap
  rw [mulVecLinR_mul, Submodule.map_comp]


def IsFullLattice (L : Submodule R (Fin 2 → K)) : Prop :=
  L.FG ∧ Submodule.span K (L : Set (Fin 2 → K)) = ⊤


def scalarGL (c : Kˣ) : Matrix.GeneralLinearGroup (Fin 2) K :=
  ⟨(c : K) • 1, ((c⁻¹ : Kˣ) : K) • 1, by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Units.mul_inv,
        one_smul], by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Units.inv_mul,
        one_smul]⟩

@[simp] theorem scalarGL_coe (c : Kˣ) :
    ((scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (c : K) • 1 := rfl


theorem scalarGL_mul_comm (c : Kˣ) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    scalarGL c * g = g * scalarGL c := by
  ext1
  rw [Units.val_mul, Units.val_mul, scalarGL_coe, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]


def Homothetic (L L' : Submodule R (Fin 2 → K)) : Prop :=
  ∃ c : Kˣ, latticeMap (scalarGL c) L = L'


theorem scalarGL_one : scalarGL (1 : Kˣ) = 1 := by
  ext1
  change (1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) = (1 : Matrix (Fin 2) (Fin 2) K)
  rw [one_smul]

theorem scalarGL_mul (c d : Kˣ) : scalarGL (c * d) = scalarGL c * scalarGL d := by
  ext1
  rw [Units.val_mul, scalarGL_coe, scalarGL_coe, scalarGL_coe, Units.val_mul,
    Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_comm]

theorem Homothetic.refl (L : Submodule R (Fin 2 → K)) : Homothetic L L :=
  ⟨1, by rw [scalarGL_one, latticeMap_one]⟩

theorem Homothetic.symm {L L' : Submodule R (Fin 2 → K)} (h : Homothetic L L') :
    Homothetic L' L := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c⁻¹, ?_⟩
  rw [← hc, ← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one,
    latticeMap_one]

theorem Homothetic.trans {L L' L'' : Submodule R (Fin 2 → K)}
    (h : Homothetic L L') (h' : Homothetic L' L'') : Homothetic L L'' := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, hd⟩ := h'
  refine ⟨d * c, ?_⟩
  rw [← hd, ← hc, ← latticeMap_mul, scalarGL_mul]

theorem IsFullLattice.map {L : Submodule R (Fin 2 → K)} (h : IsFullLattice L)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) : IsFullLattice (latticeMap g L) := by
  constructor
  · exact h.1.map (mulVecLinR g)
  · let f : (Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
      Matrix.mulVecLin (g : Matrix (Fin 2) (Fin 2) K)
    have him : (latticeMap g L : Set (Fin 2 → K)) = ⇑f '' (L : Set (Fin 2 → K)) := by
      ext v
      constructor
      · rintro ⟨x, hx, hxv⟩
        refine ⟨x, hx, ?_⟩
        exact hxv
      · rintro ⟨x, hx, hxv⟩
        refine ⟨x, hx, ?_⟩
        exact hxv
    rw [him, Submodule.span_image, h.2, Submodule.map_top]
    refine LinearMap.range_eq_top.2 ?_
    intro v
    refine ⟨(g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) *ᵥ v, ?_⟩
    calc
      f ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) *ᵥ v)
          = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ
              ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) *ᵥ v) := rfl
      _ = ((g : Matrix (Fin 2) (Fin 2) K) *
            (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K)) *ᵥ v := by
          rw [Matrix.mulVec_mulVec]
      _ = (1 : Matrix (Fin 2) (Fin 2) K) *ᵥ v := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      _ = v := Matrix.one_mulVec v
variable (R K) in

abbrev FullLattice : Type _ := {L : Submodule R (Fin 2 → K) // IsFullLattice L}

variable (R K) in

def homothetySetoid : Setoid (FullLattice R K) where
  r L L' := Homothetic L.1 L'.1
  iseqv := ⟨fun L => Homothetic.refl L.1, Homothetic.symm, Homothetic.trans⟩

variable (R K) in

def Vertex : Type _ := Quotient (homothetySetoid R K)


variable {R K} in


def Vertex.act (g : Matrix.GeneralLinearGroup (Fin 2) K) : Vertex R K → Vertex R K :=
  Quotient.map (fun L => ⟨latticeMap g L.1, L.2.map g⟩)
    (by
      rintro ⟨L, hL⟩ ⟨L', hL'⟩ ⟨c, hc⟩
      exact ⟨c, by
        show latticeMap (scalarGL c) (latticeMap g L) = latticeMap g L'
        rw [← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul, hc]⟩)


variable [IsFractionRing R K]


end LT.LatticeTree

namespace LT.LatticeTree


open Module
open scoped LinearAlgebra.Projectivization

section ResiduePlane

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]


end ResiduePlane

section NeighbourFamily

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]


variable [IsFractionRing R K]


end NeighbourFamily

section Gates

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]


variable [IsFractionRing R K]


end Gates

section PadicGates


end PadicGates

end LT.LatticeTree

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree


variable {R : Type*} [CommRing R]
variable {K : Type*} [Field K] [Algebra R K]

structure IntegralAut (R K : Type*) [CommRing R] [Field K] [Algebra R K] where

  toField : K ≃+* K

  toBase : R ≃+* R

  commutes : ∀ r : R, toField (algebraMap R K r) = algebraMap R K (toBase r)

namespace IntegralAut

def symm (σ : IntegralAut R K) : IntegralAut R K where
  toField := σ.toField.symm
  toBase := σ.toBase.symm
  commutes := by
    intro r
    have h := σ.commutes (σ.toBase.symm r)
    rw [RingEquiv.apply_symm_apply] at h
    exact (RingEquiv.eq_symm_apply σ.toField).2 h.symm

theorem symm_toField (σ : IntegralAut R K) : σ.symm.toField = σ.toField.symm := rfl

theorem symm_toBase (σ : IntegralAut R K) : σ.symm.toBase = σ.toBase.symm := rfl


end IntegralAut

attribute [local simp] IntegralAut.symm_toField IntegralAut.symm_toBase

def galVec (σ : IntegralAut R K) (v : Fin 2 → K) : Fin 2 → K :=
  fun i => σ.toField (v i)

@[simp] theorem galVec_apply (σ : IntegralAut R K) (v : Fin 2 → K) (i : Fin 2) :
    galVec σ v i = σ.toField (v i) := rfl

theorem galVec_add (σ : IntegralAut R K) (v w : Fin 2 → K) :
    galVec σ (v + w) = galVec σ v + galVec σ w := by
  funext i
  simp [galVec, map_add]

theorem galVec_zero (σ : IntegralAut R K) : galVec σ (0 : Fin 2 → K) = 0 := by
  funext i
  simp [galVec]

theorem galVec_smul (σ : IntegralAut R K) (r : R) (v : Fin 2 → K) :
    galVec σ (r • v) = σ.toBase r • galVec σ v := by
  funext i
  rw [galVec_apply, Pi.smul_apply, Pi.smul_apply, galVec_apply, Algebra.smul_def,
    Algebra.smul_def, map_mul, σ.commutes]


theorem galVec_symm_galVec (σ : IntegralAut R K) (v : Fin 2 → K) :
    galVec σ.symm (galVec σ v) = v := by
  funext i
  simp [galVec]

theorem galVec_galVec_symm (σ : IntegralAut R K) (v : Fin 2 → K) :
    galVec σ (galVec σ.symm v) = v := by
  funext i
  simp [galVec]


def latticeGal (σ : IntegralAut R K) (L : Submodule R (Fin 2 → K)) :
    Submodule R (Fin 2 → K) where
  carrier := galVec σ '' L
  add_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v + w, L.add_mem hv hw, galVec_add σ v w⟩
  zero_mem' := ⟨0, L.zero_mem, galVec_zero σ⟩
  smul_mem' := by
    rintro r _ ⟨w, hw, rfl⟩
    refine ⟨σ.toBase.symm r • w, L.smul_mem _ hw, ?_⟩
    rw [galVec_smul, RingEquiv.apply_symm_apply]


theorem galVec_mem_latticeGal {σ : IntegralAut R K} {L : Submodule R (Fin 2 → K)}
    {w : Fin 2 → K} (hw : w ∈ L) : galVec σ w ∈ latticeGal σ L :=
  ⟨w, hw, rfl⟩


theorem latticeGal_symm_latticeGal (σ : IntegralAut R K)
    (L : Submodule R (Fin 2 → K)) : latticeGal σ.symm (latticeGal σ L) = L := by
  ext v
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    rwa [galVec_symm_galVec]
  · intro hv
    exact ⟨galVec σ v, galVec_mem_latticeGal hv, galVec_symm_galVec σ v⟩

theorem latticeGal_latticeGal_symm (σ : IntegralAut R K)
    (L : Submodule R (Fin 2 → K)) : latticeGal σ (latticeGal σ.symm L) = L := by
  ext v
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    rwa [galVec_galVec_symm]
  · intro hv
    exact ⟨galVec σ.symm v, galVec_mem_latticeGal hv, galVec_galVec_symm σ v⟩


end LT.LatticeTree

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree

attribute [local simp] mem_stdLattice latticeMap_one IntegralAut.symm_toField IntegralAut.symm_toBase galVec_symm_galVec galVec_galVec_symm latticeGal_symm_latticeGal latticeGal_latticeGal_symm

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

def IsFixedVertex (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) : Prop :=
  Vertex.act g v = v

def fixedVertexSet (g : Matrix.GeneralLinearGroup (Fin 2) K) : Set (Vertex R K) :=
  {v | IsFixedVertex g v}

theorem mem_fixedVertexSet {g : Matrix.GeneralLinearGroup (Fin 2) K}
    {v : Vertex R K} : v ∈ fixedVertexSet (R := R) g ↔ Vertex.act g v = v :=
  Iff.rfl


section Engine

variable [IsFractionRing R K]


end Engine

section Dichotomy

variable [IsFractionRing R K]


end Dichotomy

section Rigidity

variable [IsFractionRing R K]


end Rigidity

section FullLattice

variable [IsFractionRing R K]


end FullLattice

section PadicGates


end PadicGates

end LT.LatticeTree

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree

attribute [local simp] mem_stdLattice latticeMap_one IntegralAut.symm_toField IntegralAut.symm_toBase galVec_symm_galVec galVec_galVec_symm latticeGal_symm_latticeGal latticeGal_latticeGal_symm mem_fixedVertexSet

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]


section FundamentalLemma

variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']


end FundamentalLemma


end LT.LatticeTree
