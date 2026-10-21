import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {k : Type*} [Field k] {ι : Type*} {n : ℕ}
private noncomputable def colAt (f : Fin n → ι → k) (i : ι) : Fin n → k := fun j => f j i
private lemma span_range_colAt_eq_top (f : Fin n → ι → k) (hf : LinearIndependent k f) :
    Submodule.span k (Set.range (colAt f)) = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  set c : Fin n → k := fun j => φ (Pi.single j 1) with hc
  have hφ : ∀ v : Fin n → k, φ v = ∑ j, v j * c j := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ φ v]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul]
    congr 2
    ext i
    simp [Pi.single_apply, eq_comm]
  have hsum : ∑ j, c j • f j = 0 := by
    ext i
    have hi : φ (colAt f i) = 0 := hle (Submodule.subset_span ⟨i, rfl⟩)
    rw [hφ] at hi
    simpa [colAt, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hi
  have hc0 : ∀ j, c j = 0 := Fintype.linearIndependent_iff.mp hf c hsum
  apply hφ0
  apply LinearMap.pi_ext'
  intro j
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single, LinearMap.zero_comp,
    LinearMap.zero_apply]
  have := hc0 j
  simp only [hc] at this
  simpa using this
private lemma exists_submatrix_det_ne_zero_of_linearIndependent (f : Fin n → ι → k) (hf : LinearIndependent k f) :
    ∃ s : Fin n → ι, Function.Injective s ∧ (Matrix.of fun l j => f j (s l)).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' k (colAt f)
  rw [span_range_colAt_eq_top f hf] at hspan
  let b : Module.Basis κ k (Fin n → k) := Module.Basis.mk hli (by rw [hspan])
  let e : Fin n ≃ κ := (b.indexEquiv (Pi.basisFun k (Fin n))).symm
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  have hrows : LinearIndependent k (Matrix.of fun l j => f j ((a ∘ e) l)).row := by
    have h2 : LinearIndependent k (colAt f ∘ a ∘ e) := (hli.comp e e.injective)
    convert h2 using 1
    rfl
  have hU : IsUnit (Matrix.of fun l j => f j ((a ∘ e) l)) := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hU).ne_zero
variable {A : Type*} [CommRing A] [IsLocalRing A] {ι : Type*} {n : ℕ}
private lemma exists_submatrix_isUnit_det_of_linearIndependent_residue (b : Fin n → ι → A)
    (hb : LinearIndependent (IsLocalRing.ResidueField A) (fun j i => IsLocalRing.residue A (b j i))) :
    ∃ s : Fin n → ι, Function.Injective s ∧ IsUnit (Matrix.of fun l j => b j (s l)).det := by
  obtain ⟨s, hs, hdet⟩ := exists_submatrix_det_ne_zero_of_linearIndependent _ hb
  refine ⟨s, hs, ?_⟩
  have hmap : IsLocalRing.residue A (Matrix.of fun l j => b j (s l)).det
      = (Matrix.of fun l j => IsLocalRing.residue A (b j (s l))).det := by
    rw [RingHom.map_det]; rfl
  have hne : IsLocalRing.residue A (Matrix.of fun l j => b j (s l)).det ≠ 0 := hmap ▸ hdet
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hne
/--
[LinearIndependent_exists_det_submatrix_ne_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearIndependent_exists_det_submatrix_ne_zero.lean)
-/
@[path]
private lemma main
    {k : Type*} [Field k] {ι : Type*} {n : ℕ}
    (f : Fin n → ι → k) (hf : LinearIndependent k f) :
    ∃ s : Fin n → ι, Function.Injective s ∧ (Matrix.of fun l j => f j (s l)).det ≠ 0 :=
  exists_submatrix_det_ne_zero_of_linearIndependent f hf

-- created on 2026-10-20
