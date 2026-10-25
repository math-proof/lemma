import Mathlib.RingTheory.Trace.Basic
import Instance.NumberField_StandardGlobalAddCharRat

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.InfinitePlace
open AutomorphicForm

noncomputable section

namespace NumberField.StandardAddChar


variable (F : Type) [Field F] [NumberField F]

structure AdelicTraceData where

  traceFin : FiniteAdeleRing (𝓞 F) F →+ FiniteAdeleRing (𝓞 ℚ) ℚ

  traceInf : InfiniteAdeleRing F →+ InfiniteAdeleRing ℚ

  traceFin_algebraMap (x : F) : traceFin (algebraMap F (FiniteAdeleRing (𝓞 F) F) x)
    = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (Algebra.trace ℚ F x)

  traceInf_algebraMap (x : F) : traceInf (algebraMap F (InfiniteAdeleRing F) x)
    = algebraMap ℚ (InfiniteAdeleRing ℚ) (Algebra.trace ℚ F x)

  continuous_traceFin : Continuous traceFin

  continuous_traceInf : Continuous traceInf

  traceInf_surjective : Function.Surjective traceInf

namespace AdelicTraceData

variable {F}
variable (T : AdelicTraceData F)


end AdelicTraceData


end NumberField.StandardAddChar

end
