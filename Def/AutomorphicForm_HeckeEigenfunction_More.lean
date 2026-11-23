import Lemma.Measure.CarrierPins
import Def.AutomorphicForm_HeckeEigensystem
import Lemma.Matrix.AdelicLevel
import Instance.AbstractHeckeOperator
import Def.AbstractHeckeOperator_Main
import Theorem.AbstractHeckeOperator_Main
import Abbrev.AutomorphicForm_HeckeEigenfunction

set_option autoImplicit false

open IsDedekindDomain NumberField MulAction Matrix.AdelicLevel Matrix
open scoped Pointwise

noncomputable section

namespace AutomorphicForm

section Defs

variable (F : Type) [Field F] [NumberField F]

def rightTranslationEmbed : AdelicGL2 (𝓞 F) F →* RightTranslationGroup F where
  toFun g := DomMulAct.mk (MulOpposite.op g)
  map_one' := rfl
  map_mul' _ _ := rfl

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


end AutomorphicForm

end
