import Lemma.Definitions.Def_HaarQuotient
import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Lemma.Definitions.Def_NumberField_TateGlobalZeta
import Lemma.Definitions.Def_M4aHerbrand_AdeleTopologyFacts

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicHaar LanglandsTunnell.CubicInduction Topology
open scoped ENNReal NNReal

namespace WhittakerBlock

def unipotentSubgroup3 : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  Subgroup.closure (Set.range fun t : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
    upperUnipotent3 t.1 t.2.1 t.2.2)

def unipotentHaar3 :
    @Measure ↥unipotentSubgroup3 (@Subtype.instMeasurableSpace _ _ (glBorel (Fin 3) (𝓞 ℚ) ℚ)) :=
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := adeleBorel (𝓞 ℚ) ℚ
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := glBorel (Fin 3) (𝓞 ℚ) ℚ
  Measure.map
    (fun t : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (⟨upperUnipotent3 t.1 t.2.1 t.2.2, Subgroup.subset_closure ⟨t, rfl⟩⟩ : unipotentSubgroup3))
    ((adelicAddHaar (𝓞 ℚ) ℚ).prod ((adelicAddHaar (𝓞 ℚ) ℚ).prod (adelicAddHaar (𝓞 ℚ) ℚ)))

def quotientMeasure :
    @Measure (MulAction.orbitRel.Quotient (unipotentSubgroup3) (AdelicGL 3 (𝓞 ℚ) ℚ))
      (@Quotient.instMeasurableSpace _ _ (glBorel (Fin 3) (𝓞 ℚ) ℚ)) :=
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := glBorel (Fin 3) (𝓞 ℚ) ℚ
  HaarQuotient.measure (adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) unipotentSubgroup3 unipotentHaar3

def zerothShell (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    Set (MulAction.orbitRel.Quotient (unipotentSubgroup3) (AdelicGL 3 (𝓞 ℚ) ℚ)) :=
  {q | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S →
    ∃ (x y z : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
      k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ componentAt3 (𝓞 ℚ) ℚ p q.out = upperUnipotent3 x y z * k}

def block (pins : AutomorphicForm.CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (σ : ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : ℝ≥0∞ :=
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := glBorel (Fin 3) (𝓞 ℚ) ℚ
  ∫⁻ q in zerothShell S,
    ((‖whittaker3 pins ψ f q.out‖₊ : ℝ≥0∞) ^ 2 *
      (‖Φ fun j : Fin 3 => (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det q.out) ^ σ))
    ∂quotientMeasure

instance sigmaCompactSpace_adelicGL3 : SigmaCompactSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := by
  haveI : SigmaCompactSpace (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
    inferInstanceAs (SigmaCompactSpace (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))
  haveI : SigmaCompactSpace (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  exact Units.isClosedEmbedding_embedProduct.sigmaCompactSpace

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
