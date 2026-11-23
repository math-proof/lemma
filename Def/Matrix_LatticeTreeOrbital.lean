module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Data.Complex.Basic
public import Structure.LatticeTreeOrbital
public import Abbrev.LatticeTreeOrbital

@[expose] public section

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree


variable (R : Type*) [CommRing R]
variable (K : Type*) [Field K] [Algebra R K]


variable {R K}


def diagSnd (x : Kˣ) : Matrix.GeneralLinearGroup (Fin 2) K :=
  ⟨Matrix.diagonal ![1, (x : K)], Matrix.diagonal ![1, ((x⁻¹ : Kˣ) : K)], by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp, by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp⟩

variable (R K) in


variable (R K) in


variable (R K) in


variable (R K) in

def Vertex.mk (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) : Vertex R K :=
  Quotient.mk (homothetySetoid R K) ⟨L, hL⟩

variable (R K) in

def stdVertex : Vertex R K := Vertex.mk R K (stdLattice R K) isFullLattice_stdLattice

variable [IsFractionRing R K]

def unitOfNeZero {ϖ : R} (hϖ : ϖ ≠ 0) : Kˣ :=
  Units.mk0 (algebraMap R K ϖ)
    (fun h => hϖ (IsFractionRing.injective R K (by rw [h, map_zero])))

def AdjacentLattice (L L' : Submodule R (Fin 2 → K)) : Prop :=
  ∃ (ϖ : R) (hϖ : Irreducible ϖ),
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) L < L' ∧ L' < L

end LT.LatticeTree

namespace LT.LatticeTree

attribute [local simp] mem_stdLattice latticeMap_one

open Module
open scoped LinearAlgebra.Projectivization

section ResiduePlane

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

set_option maxHeartbeats 800000 in

noncomputable def submoduleNeBotNeTopEquivProjectivization [FiniteDimensional k V]
    (hV : finrank k V = 2) :
    {W : Submodule k V // W ≠ ⊥ ∧ W ≠ ⊤} ≃ ℙ k V :=
  (Equiv.subtypeEquivRight (ne_bot_and_ne_top_iff_finrank_eq_one hV)).trans
    (Projectivization.equivSubmodule k V).symm


end ResiduePlane

section NeighbourFamily

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

variable (R K) in

def interLattice (ϖ c d : R) : Submodule R (Fin 2 → K) where
  carrier := {v | (∀ i, IsLocalization.IsInteger R (v i)) ∧
    ∃ w : K, IsLocalization.IsInteger R w ∧
      algebraMap R K d * v 0 - algebraMap R K c * v 1 = algebraMap R K ϖ * w}
  add_mem' := by
    rintro v u ⟨hv, wv, hwv, hv'⟩ ⟨hu, wu, hwu, hu'⟩
    refine ⟨fun i => IsLocalization.isInteger_add (hv i) (hu i),
      wv + wu, IsLocalization.isInteger_add hwv hwu, ?_⟩
    simp only [Pi.add_apply]
    linear_combination hv' + hu'
  zero_mem' := by
    refine ⟨fun _ => IsLocalization.isInteger_zero, 0, IsLocalization.isInteger_zero, ?_⟩
    simp
  smul_mem' := by
    rintro r v ⟨hv, w, hw, hv'⟩
    refine ⟨fun i => by rw [Pi.smul_apply]; exact IsLocalization.isInteger_smul (hv i),
      r • w, IsLocalization.isInteger_smul hw, ?_⟩
    simp only [Pi.smul_apply, Algebra.smul_def]
    linear_combination algebraMap R K r * hv'

variable (R K) in

def vecPair (c d : R) : Fin 2 → K := ![algebraMap R K c, algebraMap R K d]

variable [IsFractionRing R K]

variable (R K) in

noncomputable def neighborOfOption (ϖ : R) (x : Option (R ⧸ Ideal.span {ϖ})) :
    Submodule R (Fin 2 → K) :=
  x.elim (interLattice R K ϖ 0 1) (fun y => interLattice R K ϖ 1 y.out)

end NeighbourFamily


end LT.LatticeTree

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree

attribute [local simp] mem_stdLattice latticeMap_one

variable {R : Type*} [CommRing R]
variable {K : Type*} [Field K] [Algebra R K]


namespace IntegralAut

variable (R K) in

def refl : IntegralAut R K where
  toField := RingEquiv.refl K
  toBase := RingEquiv.refl R
  commutes _ := rfl

def comp (σ τ : IntegralAut R K) : IntegralAut R K where
  toField := τ.toField.trans σ.toField
  toBase := τ.toBase.trans σ.toBase
  commutes r := by
    show σ.toField (τ.toField (algebraMap R K r)) = algebraMap R K (σ.toBase (τ.toBase r))
    rw [τ.commutes, σ.commutes]

def symm (σ : IntegralAut R K) : IntegralAut R K where
  toField := σ.toField.symm
  toBase := σ.toBase.symm
  commutes := σ.symm_commutes


def mapGL (σ : IntegralAut R K) :
    Matrix.GeneralLinearGroup (Fin 2) K →* Matrix.GeneralLinearGroup (Fin 2) K :=
  Matrix.GeneralLinearGroup.map (σ.toField : K →+* K)

def unitMap (σ : IntegralAut R K) (c : Kˣ) : Kˣ where
  val := σ.toField c
  inv := σ.toField ↑c⁻¹
  val_inv := by rw [← map_mul, Units.mul_inv, map_one]
  inv_val := by rw [← map_mul, Units.inv_mul, map_one]

end IntegralAut


def Vertex.galAct (σ : IntegralAut R K) : Vertex R K → Vertex R K :=
  Quotient.map (fun L => ⟨latticeGal σ L.1, L.2.gal σ⟩)
    (by
      rintro ⟨L, hL⟩ ⟨L', hL'⟩ ⟨c, hc⟩
      refine ⟨σ.unitMap c, ?_⟩
      show latticeMap _ (latticeGal σ L) = latticeGal σ L'
      rw [← latticeGal_scalarGL, hc])

def normTwo (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) :
    Matrix.GeneralLinearGroup (Fin 2) K :=
  δ * σ.mapGL δ

def normThree (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) :
    Matrix.GeneralLinearGroup (Fin 2) K :=
  δ * σ.mapGL δ * (σ.comp σ).mapGL δ

def conjAut : IntegralAut ℂ ℂ where
  toField := starRingAut
  toBase := starRingAut
  commutes r := by
    simp [Algebra.algebraMap_self]

end LT.LatticeTree

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree


variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]


attribute [local simp] mem_fixedVertexSet
variable (R) in

noncomputable def unitOrbitalCount (g : Matrix.GeneralLinearGroup (Fin 2) K) : ℕ :=
  Nat.card (fixedVertexSet (R := R) g)

section Engine

variable [IsFractionRing R K]

def mulVecPair (M : Matrix (Fin 2) (Fin 2) R) (c d : R) : Fin 2 → R :=
  M *ᵥ ![c, d]

end Engine

section Dichotomy

variable [IsFractionRing R K]

omit [IsFractionRing R K] in

end Dichotomy

section Rigidity

variable [IsFractionRing R K]

omit [Algebra R K] [IsFractionRing R K] in

end Rigidity


section PadicGates

noncomputable def gammaZero : Matrix.GeneralLinearGroup (Fin 2) ℤ_[2] :=
  ((Matrix.isUnit_iff_isUnit_det
      (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) ℤ_[2])).mpr
    (by rw [Matrix.det_fin_two_of]; norm_num)).unit

noncomputable def transvectionGate : Matrix.GeneralLinearGroup (Fin 2) ℤ_[2] :=
  ((Matrix.isUnit_iff_isUnit_det
      (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ_[2])).mpr
    (by rw [Matrix.det_fin_two_of]; norm_num)).unit

end PadicGates

end LT.LatticeTree

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree


variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

def Vertex.twistedAct (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K)
    (v : Vertex R K) : Vertex R K :=
  Vertex.act δ (Vertex.galAct σ v)

def IsTwistedFixedVertex (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) (v : Vertex R K) : Prop :=
  Vertex.twistedAct δ σ v = v

def twistedFixedVertexSet (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) : Set (Vertex R K) :=
  {v | IsTwistedFixedVertex δ σ v}

attribute [local simp] mem_twistedFixedVertexSet
noncomputable def twistedUnitOrbitalCount (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) : ℕ :=
  Nat.card (twistedFixedVertexSet δ σ)


end LT.LatticeTree

end
