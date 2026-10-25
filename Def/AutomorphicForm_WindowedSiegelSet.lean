import Lemma.AutomorphicForm.CarrierPins
import Lemma.NumberField.AdelicLevel

open IsDedekindDomain NumberField Matrix MeasureTheory

open scoped ENNReal

noncomputable section

namespace AutomorphicForm

namespace WindowedSiegel

variable {K : Type*} [NormedField K]

def topNormSq (g : Matrix (Fin 2) (Fin 2) K) : ℝ :=
  ‖g 0 0‖ ^ 2 + ‖g 0 1‖ ^ 2

def rowNormSq (g : Matrix (Fin 2) (Fin 2) K) : ℝ :=
  ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2

def localHeight (g : GL (Fin 2) K) : ℝ :=
  ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ / rowNormSq (g : Matrix (Fin 2) (Fin 2) K)

def xWindowSq (g : GL (Fin 2) K) : ℝ :=
  topNormSq (g : Matrix (Fin 2) (Fin 2) K) / rowNormSq (g : Matrix (Fin 2) (Fin 2) K)
    - localHeight g ^ 2


variable (F : Type) [Field F] [NumberField F]

def archHeight (g : GL (Fin 2) (InfiniteAdeleRing F)) : ℝ :=
  ∏ v : InfinitePlace F, localHeight (AdelicLevel.archComponent F v g) ^ v.mult


def integralWindowedSiegelSet (c u : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | AdelicLevel.glFin (𝓞 F) F g ∈ AdelicLevel.finiteIntegralGL2 (𝓞 F) F ∧ c ≤ archHeight F (AdelicLevel.glArch (𝓞 F) F g) ∧
    ∀ v : InfinitePlace F, xWindowSq (AdelicLevel.archComponent F v (AdelicLevel.glArch (𝓞 F) F g)) ≤ u ^ 2}

def globalTranslate (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) : AdelicGL2 (𝓞 F) F :=
  globalPoints (𝓞 F) F γ * g

def siegelOverlapSet (c u : ℝ) : Set (GL (Fin 2) F) :=
  {γ | ∃ g ∈ integralWindowedSiegelSet F c u,
    globalTranslate F γ g ∈ integralWindowedSiegelSet F c u}

def WindowedSiegelProperty (c u : ℝ) : Prop :=
  (((QuotientGroup.mk : GL (Fin 2) F → GL (Fin 2) F ⧸ Subgroup.center (GL (Fin 2) F))) ''
    siegelOverlapSet F c u).Finite

def WindowedAdelicReduction (c u : ℝ) : Prop :=
  ∀ g : AdelicGL2 (𝓞 F) F, ∃ γ : GL (Fin 2) F,
    globalTranslate F γ g ∈ integralWindowedSiegelSet F c u


variable (F : Type) [Field F] [NumberField F]


def MeasureZeroOrInfiniteAt [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    (μ : Measure (AdelicGL2 (𝓞 F) F)) (c u : ℝ) : Prop :=
  μ (integralWindowedSiegelSet F c u) = 0 ∨ μ (integralWindowedSiegelSet F c u) = ⊤

end WindowedSiegel

end AutomorphicForm

end
