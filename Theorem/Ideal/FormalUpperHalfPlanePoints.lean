module

public import Mathlib
public import Theorem.Submodule.FormalUpperHalfPlaneFunctor
public import Theorem.Set.OmegaTubes
public import Structure.CerednikDrinfeld_FormalUpperHalfPlanePoints

public noncomputable section

set_option autoImplicit false

noncomputable section

open scoped TensorProduct MatrixGroups
open LT.LatticeTree TensorProduct Matrix

namespace CerednikDrinfeld
namespace FormalOmega

section ChartLoci

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]


public theorem DeligneDatum.exists_edgeNondegAt (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (h𝔭 : 𝔭.IsPrime) :
    ∃ M' M : FullLattice 𝒪 K, d.EdgeNondegAt π 𝔭 M' M := by
  obtain ⟨M', M, h, hπ, h1, h2⟩ := d.nondeg 𝔭 h𝔭
  exact ⟨M', M, h, hπ, h1, h2⟩


public theorem isNilpotent_algebraMap_modPow (n : ℕ) : IsNilpotent (algebraMap 𝒪 (modPow π R n) π) :=
  ⟨n + 1, by
    rw [← map_pow, IsScalarTower.algebraMap_apply 𝒪 R (modPow π R n), Ideal.Quotient.algebraMap_eq, map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)⟩


public theorem coordToTensor_add (n : ℕ) (w w' : Fin 2 → R) :
    coordToTensor K π R n (w + w') = coordToTensor K π R n w + coordToTensor K π R n w' := by
  simp only [coordToTensor, Pi.add_apply, map_add, add_tmul, Finset.sum_add_distrib]


public theorem coordToTensor_smul (n : ℕ) (r : R) (w : Fin 2 → R) :
    coordToTensor K π R n (r • w) =
      Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) r • coordToTensor K π R n w := by
  simp only [coordToTensor, Pi.smul_apply, smul_eq_mul, map_mul, Finset.smul_sum, smul_tmul', smul_eq_mul]


public theorem coordToTensor_zero (n : ℕ) : coordToTensor K π R n 0 = 0 := by
  simp only [coordToTensor, Pi.zero_apply, map_zero, zero_tmul, Finset.sum_const_zero]

variable {K π R}


public theorem AdicPoint.mem_stdLine_iff (x : AdicPoint K π R) (w : Fin 2 → R) :
    w ∈ x.stdLine ↔ ∀ n : ℕ, coordToTensor K π R n w ∈ (x.pt n).line (stdFullLattice K) := Iff.rfl


public theorem AdicPoint.ext' {x y : AdicPoint K π R} (h : x.pt = y.pt) : x = y := by
  cases x; cases y; cases h; rfl


public theorem AdicPoint.act_pt (g : GL (Fin 2) K) (x : AdicPoint K π R) (n : ℕ) :
    (x.act g).pt n = DeligneDatum.pullback π (modPow π R n) g⁻¹ (x.pt n) := rfl


public theorem AdicPoint.act_one (x : AdicPoint K π R) : x.act 1 = x :=
  AdicPoint.ext' (funext fun n => (Omega.action K π).act_one (modPow π R n) (x.pt n))


public theorem AdicPoint.act_mul (g h : GL (Fin 2) K) (x : AdicPoint K π R) : x.act (g * h) = (x.act h).act g :=
  AdicPoint.ext' (funext fun n => (Omega.action K π).act_mul (modPow π R n) g h (x.pt n))

variable (C : Type) [Field C] [Algebra R C]


public theorem AdicPoint.vecCons_toOmega_mem (x : AdicPoint K π R) (h : ∃! z : C, (![z, 1] : Fin 2 → C) ∈ x.lineC C) :
    (![x.toOmega C, 1] : Fin 2 → C) ∈ x.lineC C := by
  classical
  rw [AdicPoint.toOmega, dif_pos h]
  exact (Classical.choose_spec h.exists)

end AdicPoints

section Sigma

variable (K₀ : Type) [Field K₀] {C : Type} [Field C] [Algebra K₀ C]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]

omit Γ₀ in


@[simp] public theorem diagFst_coe (a : K₀ˣ) : ((diagFst K₀ a : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![(a : K₀), 1] :=
  rfl


public theorem diagFst_mulVec (a : K₀ˣ) (v : Fin 2 → K₀) :
    ((diagFst K₀ a : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) *ᵥ v = ![(a : K₀) * v 0, v 1] := by
  rw [diagFst_coe]
  funext i
  rw [Matrix.mulVec_diagonal]
  fin_cases i <;> simp

variable (ϖ : Omega.PseudoUniformizer K₀ C)


public theorem edgeFlip_ne_zero : ϖ.ϖ ≠ 0 := by
  intro h
  have := ϖ.pos
  rw [h, map_zero, map_zero] at this
  exact lt_irrefl _ this


public theorem edgeFlip_mulVec (v : Fin 2 → K₀) :
    ((edgeFlip K₀ ϖ : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) *ᵥ v = ![ϖ.ϖ * v 0, v 1] :=
  diagFst_mulVec K₀ _ v


public theorem pmoebius_edgeFlip [DecidableEq C] (z : C) :
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
