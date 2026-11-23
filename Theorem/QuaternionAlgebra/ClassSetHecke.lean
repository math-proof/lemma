module

public import Mathlib
public import Theorem.Submodule.FiniteAdeleBox
public import Def.QuaternionAlgebra_Order
public import Theorem.QuaternionAlgebra.ReducedNorm
public import Abbrev.QuaternionAlgebra_ClassSetHecke

public noncomputable section

set_option autoImplicit false

open scoped TensorProduct Pointwise Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace QuaternionAlgebra

variable {a b : ℚ}

namespace ClassSet

variable {U U' : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}

public theorem mk_surjective : Function.Surjective (mk U) := Quotient.mk''_surjective


@[simp] public theorem map_mk (h : U ≤ U') (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    map h (mk U x) = mk U' x := rfl


public theorem map_surjective (h : U ≤ U') : Function.Surjective (map h) := by
  rintro ⟨x⟩; exact ⟨mk U x, rfl⟩


public theorem mk_mul_of_mem (x u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hu : u ∈ U) :
    mk U (x * u) = mk U x :=
  ((DoubleCoset.eq _ _ _ _).mpr ⟨1, one_mem _, u, hu, by rw [one_mul]⟩).symm


public theorem mk_diagonal_mul (δ : (ℍ[ℚ, a, b])ˣ) (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    mk U (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x) = mk U x :=
  ((DoubleCoset.eq _ _ _ _).mpr
    ⟨Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ, MonoidHom.mem_range.mpr ⟨δ, rfl⟩, 1, one_mem _,
      by rw [mul_one]⟩).symm

end ClassSet

section HeckeKernel


public theorem heckeKernel_mk (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hS : ∀ u ∈ U, ∀ s ∈ S, u * s ∈ S)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (y : ClassSet U) :
    heckeKernel U S (ClassSet.mk U x) y = Nat.card (HeckeIncidence U S x y) := by
  obtain ⟨δ, u, hδ, hu, hout⟩ :=
    DoubleCoset.mk_out_eq_mul (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range U x
  unfold heckeKernel
  rw [show (ClassSet.mk U x).out = δ * x * u from hout]
  have e1 : HeckeIncidence U S (δ * x * u) y ≃ HeckeIncidence U S (δ * x) y :=
    heckeIncidenceEquiv U S hS (δ * x) u hu y
  have e2 : HeckeIncidence U S (δ * x) y ≃ HeckeIncidence U S x y := by
    refine Equiv.subtypeEquivRight fun c => ?_
    obtain ⟨δ', rfl⟩ := MonoidHom.mem_range.mp hδ
    simp only [mul_assoc, ClassSet.mk_diagonal_mul]
  rw [Nat.card_congr (e1.trans e2)]

end HeckeKernel

section Level


public theorem mem_primeHeckeSet_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ)
    (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    h ∈ primeHeckeSet Λ ℓ ↔
      (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ ∧
      (ℓ : ℚ) • ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ ∧
      ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
          ∉ Submodule.finiteAdeleBox Λ ∧
      (ℓ : ℚ)⁻¹ • (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∉ Submodule.finiteAdeleBox Λ :=
  Iff.rfl


public theorem mem_levelHeckeSet_iff (Λ P : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ)
    (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    h ∈ levelHeckeSet Λ P ℓ ↔
      h ∈ primeHeckeSet Λ ℓ ∧
        (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) - 1 ∈ Submodule.finiteAdeleBox P :=
  Iff.rfl


public theorem mem_congruenceLevel_iff (Λ P : Submodule ℤ ℍ[ℚ, a, b])
    (u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    u ∈ congruenceLevel Λ P ↔
      u ∈ Submodule.finiteIdeleStabilizer Λ ∧ u ∈ Submodule.finiteIdeleStabilizer P ∧
        ∀ x ∈ Submodule.finiteAdeleBox Λ,
          (u : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * x - x ∈ Submodule.finiteAdeleBox P :=
  Iff.rfl


public theorem congruenceLevel_le (Λ P : Submodule ℤ ℍ[ℚ, a, b]) :
    congruenceLevel Λ P ≤ Submodule.finiteIdeleStabilizer Λ := fun _ hu => hu.1


public theorem mul_mul_mem_normIdeal {Λ : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} {x y z : ℍ[ℚ, a, b]}
    (hx : x ∈ Λ) (hy : y ∈ Λ) (hz : z ∈ Λ) (m : ℤ) (hm : nrd y = (q : ℚ) * m) :
    x * y * z ∈ normIdeal Λ q :=
  Submodule.subset_span ⟨x, hx, y, hy, z, hz, ⟨m, hm⟩, rfl⟩


public theorem IsOrder.normIdeal_le {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (q : ℕ) :
    normIdeal Λ q ≤ Λ := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, hx, y, hy, z, hz, -, rfl⟩
  exact hΛ.mul_mem (hΛ.mul_mem hx hy) hz


public theorem IsOrder.mul_mem_normIdeal {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {q : ℕ}
    {x w : ℍ[ℚ, a, b]} (hx : x ∈ Λ) (hw : w ∈ normIdeal Λ q) : x * w ∈ normIdeal Λ q := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x', hx', y, hy, z, hz, ⟨m, hm⟩, rfl⟩ := hw
    simpa only [mul_assoc] using mul_mul_mem_normIdeal (hΛ.mul_mem hx hx') hy hz m hm
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
  | smul n u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ n hu


public theorem IsOrder.mul_mem_normIdeal_right {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {q : ℕ}
    {w z : ℍ[ℚ, a, b]} (hw : w ∈ normIdeal Λ q) (hz : z ∈ Λ) : w * z ∈ normIdeal Λ q := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, y, hy, z', hz', ⟨m, hm⟩, rfl⟩ := hw
    simpa only [mul_assoc] using mul_mul_mem_normIdeal hx hy (hΛ.mul_mem hz' hz) m hm
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | smul n u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ n hu


public theorem IsOrder.natCast_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (n : ℕ) :
    (n : ℍ[ℚ, a, b]) ∈ Λ := by
  simpa using Submodule.smul_mem Λ (n : ℤ) hΛ.one_mem


public theorem IsOrder.natCast_mul_mem_normIdeal {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (q : ℕ)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : (q : ℍ[ℚ, a, b]) * x ∈ normIdeal Λ q := by
  have h := mul_mul_mem_normIdeal (q := q) hΛ.one_mem (hΛ.natCast_mem q) hx (q : ℤ) (by
    rw [show (q : ℍ[ℚ, a, b]) = ((q : ℚ) : ℍ[ℚ, a, b]) by norm_cast, nrd_coe]; push_cast; ring)
  simpa using h


public theorem IsOrder.natCast_smul_mem_normIdeal {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (q : ℕ)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : ((q : ℕ) : ℤ) • x ∈ normIdeal Λ q := by
  have h := hΛ.natCast_mul_mem_normIdeal q hx
  rwa [show (q : ℍ[ℚ, a, b]) * x = ((q : ℕ) : ℤ) • x by
    rw [zsmul_eq_mul, Int.cast_natCast]] at h

end Level

end QuaternionAlgebra

end
