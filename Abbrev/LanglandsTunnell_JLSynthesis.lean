module

public import Structure.LanglandsTunnell_JLConverse
public import Structure.AutomorphicForm_CarrierPins
public import Def.NumberField_AdelicBox
public import Def.AutomorphicForm_CentreCutSiegelSet

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel
open LanglandsTunnell.Converse

@[expose] public noncomputable section

namespace LanglandsTunnell.Converse.CuspSynthesis

open AutomorphicForm.SmoothCusp

variable {K : Type} [Field K] [NumberField K]

section WeakApproximation

open scoped WithZero

end WeakApproximation

section Components

open scoped WithZero

end Components

noncomputable abbrev pinsOf (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) :
    CarrierPins K :=
  productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
    (adelicBox K)

end LanglandsTunnell.Converse.CuspSynthesis

end
