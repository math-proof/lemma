import Mathlib
import Lemma.CerednikDrinfeld.FormalUpperHalfPlaneFunctor
import Lemma.CerednikDrinfeld.OmegaTubes
import Structure.CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option autoImplicit false

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

theorem DeligneDatum.exists_edgeNondegAt (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (h𝔭 : 𝔭.IsPrime) :
    ∃ M' M : FullLattice 𝒪 K, d.EdgeNondegAt π 𝔭 M' M := by
  obtain ⟨M', M, h, hπ, h1, h2⟩ := d.nondeg 𝔭 h𝔭
  exact ⟨M', M, h, hπ, h1, h2⟩

def DeligneDatum.InVertexChart (d : DeligneDatum (K := K) π B) (M : FullLattice 𝒪 K) : Prop :=
  ∀ 𝔭 : Ideal B, 𝔭.IsPrime → d.VertexNondegAt π 𝔭 M

def DeligneDatum.InEdgeChart (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K) : Prop :=
  ∀ 𝔭 : Ideal B, 𝔭.IsPrime → d.EdgeNondegAt π 𝔭 M' M

end ChartLoci

section AdicPoints

variable {𝒪 : Type} [CommRing 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (R : Type) [CommRing R] [Algebra 𝒪 R]


theorem isNilpotent_algebraMap_modPow (n : ℕ) : IsNilpotent (algebraMap 𝒪 (modPow π R n) π) :=
  ⟨n + 1, by
    rw [← map_pow, IsScalarTower.algebraMap_apply 𝒪 R (modPow π R n), Ideal.Quotient.algebraMap_eq, map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)⟩


def stdFullLattice : FullLattice 𝒪 K := ⟨stdLattice 𝒪 K, isFullLattice_stdLattice⟩

def stdBasisVec (i : Fin 2) : ↥(stdFullLattice (𝒪 := 𝒪) K).1 :=
  ⟨Pi.single i 1, single_one_mem_stdLattice 𝒪 K i⟩

def coordToTensor (n : ℕ) (w : Fin 2 → R) : latticeBaseChange 𝒪 K (modPow π R n) (stdFullLattice K) :=
  ∑ i : Fin 2, (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (w i)) ⊗ₜ[𝒪] stdBasisVec K i

theorem coordToTensor_add (n : ℕ) (w w' : Fin 2 → R) :
    coordToTensor K π R n (w + w') = coordToTensor K π R n w + coordToTensor K π R n w' := by
  simp only [coordToTensor, Pi.add_apply, map_add, add_tmul, Finset.sum_add_distrib]

theorem coordToTensor_smul (n : ℕ) (r : R) (w : Fin 2 → R) :
    coordToTensor K π R n (r • w) =
      Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) r • coordToTensor K π R n w := by
  simp only [coordToTensor, Pi.smul_apply, smul_eq_mul, map_mul, Finset.smul_sum, smul_tmul', smul_eq_mul]

theorem coordToTensor_zero (n : ℕ) : coordToTensor K π R n 0 = 0 := by
  simp only [coordToTensor, Pi.zero_apply, map_zero, zero_tmul, Finset.sum_const_zero]

variable {K π R}

def AdicPoint.stdLine (x : AdicPoint K π R) : Submodule R (Fin 2 → R) where
  carrier := {w | ∀ n : ℕ, coordToTensor K π R n w ∈ (x.pt n).line (stdFullLattice K)}
  zero_mem' n := by rw [coordToTensor_zero]; exact zero_mem _
  add_mem' {w w'} hw hw' n := by rw [coordToTensor_add]; exact add_mem (hw n) (hw' n)
  smul_mem' r {w} hw n := by rw [coordToTensor_smul]; exact Submodule.smul_mem _ _ (hw n)

theorem AdicPoint.mem_stdLine_iff (x : AdicPoint K π R) (w : Fin 2 → R) :
    w ∈ x.stdLine ↔ ∀ n : ℕ, coordToTensor K π R n w ∈ (x.pt n).line (stdFullLattice K) := Iff.rfl

theorem AdicPoint.ext' {x y : AdicPoint K π R} (h : x.pt = y.pt) : x = y := by
  cases x; cases y; cases h; rfl

def AdicPoint.act (g : GL (Fin 2) K) (x : AdicPoint K π R) : AdicPoint K π R where
  pt n := (Omega.action K π).act (modPow π R n) g (x.pt n)
  compat n := by
    have h := (Omega.action K π).act_map (modPowTransition π R n) g (x.pt (n + 1))
    change DeligneDatum.map π (modPowTransition π R n) ((Omega.action K π).act (modPow π R (n + 1)) g (x.pt (n + 1))) =
      (Omega.action K π).act (modPow π R n) g (DeligneDatum.map π (modPowTransition π R n) (x.pt (n + 1))) at h
    rw [h, x.compat]

theorem AdicPoint.act_pt (g : GL (Fin 2) K) (x : AdicPoint K π R) (n : ℕ) :
    (x.act g).pt n = DeligneDatum.pullback π (modPow π R n) g⁻¹ (x.pt n) := rfl

theorem AdicPoint.act_one (x : AdicPoint K π R) : x.act 1 = x :=
  AdicPoint.ext' (funext fun n => (Omega.action K π).act_one (modPow π R n) (x.pt n))

theorem AdicPoint.act_mul (g h : GL (Fin 2) K) (x : AdicPoint K π R) : x.act (g * h) = (x.act h).act g :=
  AdicPoint.ext' (funext fun n => (Omega.action K π).act_mul (modPow π R n) g h (x.pt n))

variable (C : Type) [Field C] [Algebra R C]

def AdicPoint.lineC (x : AdicPoint K π R) : Submodule C (Fin 2 → C) :=
  Submodule.span C ((fun w : Fin 2 → R => fun i => algebraMap R C (w i)) '' (x.stdLine : Set (Fin 2 → R)))

open Classical in

def AdicPoint.toOmega (x : AdicPoint K π R) : C :=
  if h : ∃! z : C, (![z, 1] : Fin 2 → C) ∈ x.lineC C then Classical.choose h.exists else 0

theorem AdicPoint.vecCons_toOmega_mem (x : AdicPoint K π R) (h : ∃! z : C, (![z, 1] : Fin 2 → C) ∈ x.lineC C) :
    (![x.toOmega C, 1] : Fin 2 → C) ∈ x.lineC C := by
  classical
  rw [AdicPoint.toOmega, dif_pos h]
  exact (Classical.choose_spec h.exists)

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

@[simp] theorem diagFst_coe (a : K₀ˣ) : ((diagFst K₀ a : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![(a : K₀), 1] :=
  rfl

theorem diagFst_mulVec (a : K₀ˣ) (v : Fin 2 → K₀) :
    ((diagFst K₀ a : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) *ᵥ v = ![(a : K₀) * v 0, v 1] := by
  rw [diagFst_coe]
  funext i
  rw [Matrix.mulVec_diagonal]
  fin_cases i <;> simp

variable (ϖ : Omega.PseudoUniformizer K₀ C)

theorem edgeFlip_ne_zero : ϖ.ϖ ≠ 0 := by
  intro h
  have := ϖ.pos
  rw [h, map_zero, map_zero] at this
  exact lt_irrefl _ this

def edgeFlip : GL (Fin 2) K₀ := diagFst K₀ (Units.mk0 ϖ.ϖ (edgeFlip_ne_zero K₀ ϖ))

theorem edgeFlip_mulVec (v : Fin 2 → K₀) :
    ((edgeFlip K₀ ϖ : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) *ᵥ v = ![ϖ.ϖ * v 0, v 1] :=
  diagFst_mulVec K₀ _ v

theorem pmoebius_edgeFlip [DecidableEq C] (z : C) :
    Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk (edgeFlip K₀ ϖ)) z = algebraMap K₀ C ϖ.ϖ * z := by
  have h10 : (edgeFlip K₀ ϖ : GL (Fin 2) K₀) 1 0 = 0 := by
    show Matrix.diagonal ![ϖ.ϖ, (1 : K₀)] 1 0 = 0
    simp
  have h11 : (edgeFlip K₀ ϖ : GL (Fin 2) K₀) 1 1 = 1 := by
    show Matrix.diagonal ![ϖ.ϖ, (1 : K₀)] 1 1 = 1
    simp
  have h00 : (edgeFlip K₀ ϖ : GL (Fin 2) K₀) 0 0 = ϖ.ϖ := by
    show Matrix.diagonal ![ϖ.ϖ, (1 : K₀)] 0 0 = ϖ.ϖ
    simp
  have h01 : (edgeFlip K₀ ϖ : GL (Fin 2) K₀) 0 1 = 0 := by
    show Matrix.diagonal ![ϖ.ϖ, (1 : K₀)] 0 1 = 0
    simp
  rw [Omega.pmoebius_mk K₀ (edgeFlip K₀ ϖ) z (by rw [h10, h11, map_zero, zero_mul, zero_add, map_one]; exact one_ne_zero),
    Omega.moebius, h10, h11, h00, h01, map_zero, map_one, zero_mul, zero_add, add_zero, div_one]

end Sigma

end FormalOmega
end CerednikDrinfeld

end
