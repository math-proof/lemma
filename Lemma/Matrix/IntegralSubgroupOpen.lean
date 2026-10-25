import Mathlib
import Lemma.LocalLanglands.LocalHeckeInstance

set_option autoImplicit false

open Matrix

namespace LocalGL2

lemma exists_entry_eq_of_mem_integralSubgroup {R : Type*} [CommRing R]
    {K : Type*} [Field K] [Algebra R K] {x : GL (Fin 2) K}
    (hx : x ∈ integralSubgroup R K) (i j : Fin 2) :
    ∃ r : R, algebraMap R K r = (x : Matrix (Fin 2) (Fin 2) K) i j := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨(y : Matrix (Fin 2) (Fin 2) R) i j, rfl⟩

end LocalGL2

namespace FLT.SpectralSide

theorem mem_integralSubgroup_iff_entries_mem {R : Type*} [CommRing R]
    {K : Type*} [Field K] [Algebra R K] (hinj : Function.Injective (algebraMap R K))
    (g : GL (Fin 2) K) :
    g ∈ LocalGL2.integralSubgroup R K
      ↔ (∀ i j, (g : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K))
        ∧ (∀ i j, ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
            ∈ Set.range (algebraMap R K)) := by
  constructor
  · intro hg
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · obtain ⟨r, hr⟩ := LocalGL2.exists_entry_eq_of_mem_integralSubgroup hg i j
      exact ⟨r, hr⟩
    · obtain ⟨r, hr⟩ :=
        LocalGL2.exists_entry_eq_of_mem_integralSubgroup (inv_mem hg) i j
      exact ⟨r, hr⟩
  · rintro ⟨hg, hginv⟩
    set A : Matrix (Fin 2) (Fin 2) R := fun i j => (hg i j).choose with hA
    set B : Matrix (Fin 2) (Fin 2) R := fun i j => (hginv i j).choose with hB
    have hAspec : ∀ i j, algebraMap R K (A i j) = (g : Matrix (Fin 2) (Fin 2) K) i j :=
      fun i j => (hg i j).choose_spec
    have hBspec : ∀ i j,
        algebraMap R K (B i j) = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j :=
      fun i j => (hginv i j).choose_spec
    have hmapA : (A.map (algebraMap R K)) = (g : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      exact hAspec i j
    have hmapB : (B.map (algebraMap R K))
        = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      exact hBspec i j
    have hmatinj : Function.Injective fun M : Matrix (Fin 2) (Fin 2) R =>
        M.map (algebraMap R K) := fun M M' hMM' => by
      ext i j
      apply hinj
      have := congrFun (congrFun hMM' i) j
      simpa [Matrix.map_apply] using this
    have hAB : A * B = 1 := by
      apply hmatinj
      simp only [Matrix.map_mul, Matrix.map_one (algebraMap R K) (map_zero _) (map_one _),
        hmapA, hmapB]
      exact (Units.mul_inv g)
    have hBA : B * A = 1 := by
      apply hmatinj
      simp only [Matrix.map_mul, Matrix.map_one (algebraMap R K) (map_zero _) (map_one _),
        hmapA, hmapB]
      exact (Units.inv_mul g)
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    apply Units.ext
    exact hmapA

theorem range_algebraMap_padicInt (p : ℕ) [Fact p.Prime] :
    Set.range (algebraMap ℤ_[p] ℚ_[p]) = Set.range ((↑) : ℤ_[p] → ℚ_[p]) := by
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, (PadicInt.algebraMap_apply r).symm⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, PadicInt.algebraMap_apply r⟩

theorem isOpen_coe_integralSubgroup_padic (p : ℕ) [Fact p.Prime] :
    IsOpen ((LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] : Set (GL (Fin 2) ℚ_[p]))) := by
  have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := fun a b hab => by
    have ha := PadicInt.algebraMap_apply (p := p) a
    have hb := PadicInt.algebraMap_apply (p := p) b
    rw [ha, hb] at hab
    exact Subtype.coe_injective hab
  have hOopen : IsOpen (Set.range (algebraMap ℤ_[p] ℚ_[p])) := by
    rw [range_algebraMap_padicInt p]
    exact PadicInt.isOpenEmbedding_coe.isOpen_range
  have hchar : (LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] : Set (GL (Fin 2) ℚ_[p]))
      = (⋂ i, ⋂ j, {g : GL (Fin 2) ℚ_[p] |
            (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j ∈ Set.range (algebraMap ℤ_[p] ℚ_[p])})
        ∩ (⋂ i, ⋂ j, {g : GL (Fin 2) ℚ_[p] |
            ((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j
              ∈ Set.range (algebraMap ℤ_[p] ℚ_[p])}) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact mem_integralSubgroup_iff_entries_mem hinj g
  rw [hchar]
  refine IsOpen.inter ?_ ?_
  · refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact hOopen.preimage (Units.continuous_val.matrix_elem i j)
  · refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact hOopen.preimage (Units.continuous_coe_inv.matrix_elem i j)

end FLT.SpectralSide
