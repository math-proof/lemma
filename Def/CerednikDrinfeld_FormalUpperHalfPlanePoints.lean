module
public import Mathlib
public import Theorem.Submodule.FormalUpperHalfPlaneFunctor
public import Theorem.Set.OmegaTubes
public import Structure.CerednikDrinfeld_FormalUpperHalfPlanePoints
set_option autoImplicit false


public section

noncomputable section

open scoped TensorProduct MatrixGroups
open LT.LatticeTree TensorProduct Matrix

namespace CerednikDrinfeld
namespace FormalOmega

section ChartLoci

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

def DeligneDatum.VertexNondegAt (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (M : FullLattice 𝒪 K) : Prop :=
  ∀ v : ↥M.1, (¬ ∃ w : ↥M.1, (v : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)) →
    (1 : B) ⊗ₜ[𝒪] v ∉ d.line M ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))

def DeligneDatum.EdgeNondegAt (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (M' M : FullLattice 𝒪 K) : Prop :=
  M'.1 ≤ M.1 ∧ (∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M'.1) ∧
    (∀ v : ↥M.1, (v : Fin 2 → K) ∉ M'.1 →
      (1 : B) ⊗ₜ[𝒪] v ∉ d.line M ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) ∧
    (∀ v' : ↥M'.1, (¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)) →
      (1 : B) ⊗ₜ[𝒪] v' ∉ d.line M' ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M')))

def DeligneDatum.InVertexChart (d : DeligneDatum (K := K) π B) (M : FullLattice 𝒪 K) : Prop :=
  ∀ 𝔭 : Ideal B, 𝔭.IsPrime → d.VertexNondegAt π 𝔭 M

def DeligneDatum.InEdgeChart (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K) : Prop :=
  ∀ 𝔭 : Ideal B, 𝔭.IsPrime → d.EdgeNondegAt π 𝔭 M' M

end ChartLoci

section AdicPoints

variable {𝒪 : Type} [CommRing 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (R : Type) [CommRing R] [Algebra 𝒪 R]


def stdFullLattice : FullLattice 𝒪 K := ⟨stdLattice 𝒪 K, isFullLattice_stdLattice⟩

def stdBasisVec (i : Fin 2) : ↥(stdFullLattice (𝒪 := 𝒪) K).1 :=
  ⟨Pi.single i 1, single_one_mem_stdLattice 𝒪 K i⟩

def coordToTensor (n : ℕ) (w : Fin 2 → R) : latticeBaseChange 𝒪 K (modPow π R n) (stdFullLattice K) :=
  ∑ i : Fin 2, (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (w i)) ⊗ₜ[𝒪] stdBasisVec K i

variable {K π R}

def AdicPoint.stdLine (x : AdicPoint K π R) : Submodule R (Fin 2 → R) where
  carrier := {w | ∀ n : ℕ, coordToTensor K π R n w ∈ (x.pt n).line (stdFullLattice K)}
  zero_mem' n := by rw [coordToTensor_zero]; exact zero_mem _
  add_mem' {w w'} hw hw' n := by rw [coordToTensor_add]; exact add_mem (hw n) (hw' n)
  smul_mem' r {w} hw n := by rw [coordToTensor_smul]; exact Submodule.smul_mem _ _ (hw n)

def AdicPoint.act (g : GL (Fin 2) K) (x : AdicPoint K π R) : AdicPoint K π R where
  pt n := (Omega.action K π).act (modPow π R n) g (x.pt n)
  compat n := by
    have h := (Omega.action K π).act_map (modPowTransition π R n) g (x.pt (n + 1))
    change DeligneDatum.map π (modPowTransition π R n) ((Omega.action K π).act (modPow π R (n + 1)) g (x.pt (n + 1))) =
      (Omega.action K π).act (modPow π R n) g (DeligneDatum.map π (modPowTransition π R n) (x.pt (n + 1))) at h
    rw [h, x.compat]

variable (C : Type) [Field C] [Algebra R C]

def AdicPoint.lineC (x : AdicPoint K π R) : Submodule C (Fin 2 → C) :=
  Submodule.span C ((fun w : Fin 2 → R => fun i => algebraMap R C (w i)) '' (x.stdLine : Set (Fin 2 → R)))

open Classical in

def AdicPoint.toOmega (x : AdicPoint K π R) : C :=
  if h : ∃! z : C, (![z, 1] : Fin 2 → C) ∈ x.lineC C then Classical.choose h.exists else 0

end AdicPoints

section Sigma

variable (K₀ : Type) [Field K₀] {C : Type} [Field C] [Algebra K₀ C]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]

omit Γ₀ in

def diagFst (a : K₀ˣ) : GL (Fin 2) K₀ :=
  ⟨Matrix.diagonal ![(a : K₀), 1], Matrix.diagonal ![((a⁻¹ : K₀ˣ) : K₀), 1], by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp, by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp⟩

variable (ϖ : Omega.PseudoUniformizer K₀ C)

def edgeFlip : GL (Fin 2) K₀ := diagFst K₀ (Units.mk0 ϖ.ϖ (edgeFlip_ne_zero K₀ ϖ))

end Sigma

end FormalOmega
end CerednikDrinfeld

end
