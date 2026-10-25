import Def.HaarQuotient
import Lemma.LanglandsTunnell.CubicInduction_Structure
import Lemma.NumberField.TateGlobalZeta
import Instance.M4aHerbrand_AdeleTopologyFacts
import Instance.LanglandsTunnell_CubicInduction_WhittakerBlock
import Def.LanglandsTunnell_CubicInduction_WhittakerBlock

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicHaar LanglandsTunnell.CubicInduction Topology
open scoped ENNReal NNReal

namespace WhittakerBlock


section Heisenberg

variable {A : Type*} [CommRing A]

private theorem upperUnipotent3_mul (x y z x' y' z' : A) :
    upperUnipotent3 x y z * upperUnipotent3 x' y' z' = upperUnipotent3 (x + x') (y + y') (z + z' + x * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

private theorem upperUnipotent3_inv (x y z : A) :
    (upperUnipotent3 x y z)⁻¹ = upperUnipotent3 (-x) (-y) (x * y - z) := by
  rw [inv_eq_iff_mul_eq_one, upperUnipotent3_mul, show x + -x = 0 by ring, show y + -y = 0 by ring,
    show z + (x * y - z) + x * -y = 0 by ring, upperUnipotent3_zero]

end Heisenberg

theorem mem_unipotentSubgroup3_iff (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    g ∈ unipotentSubgroup3 ↔ ∃ x y z : AdeleRing (𝓞 ℚ) ℚ, g = upperUnipotent3 x y z := by
  refine ⟨fun hg => ?_, fun ⟨x, y, z, h⟩ => h ▸ Subgroup.subset_closure ⟨(x, y, z), rfl⟩⟩
  unfold unipotentSubgroup3 at hg
  induction hg using Subgroup.closure_induction with
  | mem _ h => obtain ⟨t, rfl⟩ := h; exact ⟨t.1, t.2.1, t.2.2, rfl⟩
  | one => exact ⟨0, 0, 0, upperUnipotent3_zero.symm⟩
  | mul _ _ _ _ h h' =>
    obtain ⟨x, y, z, rfl⟩ := h
    obtain ⟨x', y', z', rfl⟩ := h'
    exact ⟨_, _, _, upperUnipotent3_mul x y z x' y' z'⟩
  | inv _ _ h =>
    obtain ⟨x, y, z, rfl⟩ := h
    exact ⟨_, _, _, upperUnipotent3_inv x y z⟩

theorem coe_unipotentSubgroup3_eq :
    ((unipotentSubgroup3 : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)) : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) =
      {g : AdelicGL 3 (𝓞 ℚ) ℚ |
        (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 0 0 = 1 ∧
        (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 1 1 = 1 ∧
        (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 2 = 1 ∧
        (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 1 0 = 0 ∧
        (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 0 = 0 ∧
        (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 1 = 0} := by
  ext g
  simp only [SetLike.mem_coe, Set.mem_setOf_eq, mem_unipotentSubgroup3_iff]
  constructor
  · rintro ⟨x, y, z, rfl⟩
    simp
  · rintro ⟨h00, h11, h22, h10, h20, h21⟩
    refine ⟨(g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 0 1, (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 1 2,
      (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 0 2, ?_⟩
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp [h00, h11, h22, h10, h20, h21]

theorem isClosed_unipotentSubgroup3 :
    IsClosed ((unipotentSubgroup3 : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)) : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) := by
  rw [coe_unipotentSubgroup3_eq]
  have hc : ∀ i j : Fin 3,
      Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have hz : ∀ (i j : Fin 3) (c : AdeleRing (𝓞 ℚ) ℚ),
      IsClosed {g : AdelicGL 3 (𝓞 ℚ) ℚ | (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j = c} :=
    fun i j c => isClosed_singleton.preimage (hc i j)
  simp only [Set.setOf_and]
  exact (hz 0 0 1).inter ((hz 1 1 1).inter ((hz 2 2 1).inter ((hz 1 0 0).inter ((hz 2 0 0).inter (hz 2 1 0)))))

end WhittakerBlock

end
