import Lemma.AutomorphicForm.CarrierPins
import Def.AutomorphicForm_HeckeEigensystem
import Lemma.NumberField.AdelicLevel
import Instance.AbstractHeckeOperator
import Lemma.AbstractHeckeOperator.Main
import Abbrev.AutomorphicForm_HeckeEigenfunction

set_option autoImplicit false

open IsDedekindDomain NumberField MulAction NumberField.AdelicLevel
open scoped Pointwise

noncomputable section

namespace AutomorphicForm

section Defs

variable (F : Type) [Field F] [NumberField F]

def rightTranslationEmbed : AdelicGL2 (𝓞 F) F →* RightTranslationGroup F where
  toFun g := DomMulAct.mk (MulOpposite.op g)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem rightTranslationEmbed_smul_apply (g x : AdelicGL2 (𝓞 F) F)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    (rightTranslationEmbed F g • φ) x = φ (x * g) := rfl

def uniformizerIdele (v : HeightOneSpectrum (𝓞 F)) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v (uniformizerUnit F v))

end Defs

variable {F : Type} [Field F] [NumberField F]

def levelRT (pins : CarrierPins F) (N : Ideal (𝓞 F)) :
    Subgroup (RightTranslationGroup F) :=
  (pins.U N).map (rightTranslationEmbed F)

def IsHeckeEigenfunctionOf (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (Φ : HeckeEigensystem F ℂ) : Prop :=
  ∃ hmem : φ ∈ fixedPoints (levelRT pins Φ.level) (AdelicGL2 (𝓞 F) F → ℂ),
    ∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ Φ.level →
      (∃ hfin : (QuotientGroup.mk ''
            ((levelRT pins Φ.level : Set (RightTranslationGroup F))
              * {rightTranslationEmbed F (pins.gen v)}) :
            Set (RightTranslationGroup F ⧸ levelRT pins Φ.level)).Finite,
        AbstractHeckeOperator.HeckeOperator (R := ℂ)
            (rightTranslationEmbed F (pins.gen v))
            (levelRT pins Φ.level) (levelRT pins Φ.level) hfin ⟨φ, hmem⟩
          = Φ.a v •
            (⟨φ, hmem⟩ : fixedPoints (levelRT pins Φ.level) (AdelicGL2 (𝓞 F) F → ℂ)))
      ∧ ∃ hz : uniformizerIdele F v ∈ pins.Z,
          Φ.b v = (Nat.card ((𝓞 F) ⧸ v.asIdeal) : ℂ)
            * ((ξ ⟨uniformizerIdele F v, hz⟩ : ℂˣ) : ℂ)

namespace IsHeckeEigenfunctionOf

theorem agreesAwayFromFinite_of_level_eq {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} {Φ Φ' : HeckeEigensystem F ℂ}
    (h : IsHeckeEigenfunctionOf pins ξ φ Φ) (h' : IsHeckeEigenfunctionOf pins ξ φ Φ')
    (hlev : Φ.level = Φ'.level) (hnz : ∃ x, φ x ≠ 0) :
    HeckeEigensystem.AgreesAwayFromFinite Φ Φ' := by
  obtain ⟨x₀, hx₀⟩ := hnz
  obtain ⟨N', hN', a', b'⟩ := Φ'
  dsimp only at hlev
  subst hlev
  obtain ⟨hmem, hcl⟩ := h
  obtain ⟨hmem', hcl'⟩ := h'
  have hfactors : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Φ.level}.Finite :=
    Ideal.finite_factors (by simpa using Φ.level_ne_bot)
  refine ⟨hfactors.toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv
  obtain ⟨⟨hfin, heig⟩, hz, hb⟩ := hcl v hv
  obtain ⟨⟨hfin', heig'⟩, hz', hb'⟩ := hcl' v hv
  constructor
  · have hEq :
        Φ.a v • (⟨φ, hmem⟩ :
            fixedPoints (levelRT pins Φ.level) (AdelicGL2 (𝓞 F) F → ℂ))
          = a' v • (⟨φ, hmem⟩ :
            fixedPoints (levelRT pins Φ.level) (AdelicGL2 (𝓞 F) F → ℂ)) :=
      heig.symm.trans heig'
    have hval := congrArg Subtype.val hEq
    rw [FixedPoints.coe_smul, FixedPoints.coe_smul] at hval
    have hpt := congrFun hval x₀
    simp only [Pi.smul_apply, smul_eq_mul] at hpt
    exact mul_right_cancel₀ hx₀ hpt
  · exact hb.trans hb'.symm

end IsHeckeEigenfunctionOf

theorem isHeckeEigenfunctionOf_zero_inhabitant :
    ∃ (pins : CarrierPins ℚ) (ξ : pins.Z →* ℂˣ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
      (Φ : HeckeEigensystem ℚ ℂ), IsHeckeEigenfunctionOf pins ξ φ Φ := by
  refine ⟨⟨⊤, 0, ∅, ⊤, fun _ => ⊥, fun _ => 1, ⊤, 0⟩, 1, (fun _ => (0 : ℂ)),
    ⟨⊤, by simp, fun _ => 0,
      fun v => (Nat.card ((𝓞 ℚ) ⧸ v.asIdeal) : ℂ) * 1⟩, ?_⟩
  have hmem0 : (fun _ => (0 : ℂ)) ∈
      fixedPoints (levelRT (F := ℚ) ⟨⊤, 0, ∅, ⊤, fun _ => ⊥, fun _ => 1, ⊤, 0⟩ ⊤)
        (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) := fun _ => smul_zero _
  refine ⟨hmem0, fun v _ => ⟨⟨?_, ?_⟩, Subgroup.mem_top _, rfl⟩⟩
  · refine Set.Finite.image _ (Set.Finite.subset (Set.finite_singleton 1) ?_)
    rintro x ⟨u, hu, y, hy, rfl⟩
    rcases hy with rfl
    have hu1 : u = 1 := by
      rcases hu with ⟨w, hw, rfl⟩
      rcases hw with rfl
      exact map_one _
    simp [hu1]
  · have hzero : (⟨(fun _ => (0 : ℂ)), hmem0⟩ :
        fixedPoints (levelRT (F := ℚ) ⟨⊤, 0, ∅, ⊤, fun _ => ⊥, fun _ => 1, ⊤, 0⟩ ⊤)
          (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) = 0 := Subtype.ext rfl
    rw [hzero, map_zero]
    exact Subtype.ext (by sorry)

end AutomorphicForm

end
