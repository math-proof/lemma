import Mathlib.RingTheory.Trace.Basic
import Lemma.NumberField.StandardGlobalAddCharRat
import Structure.NumberField_StandardGlobalAddChar

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.InfinitePlace
open AutomorphicForm

noncomputable section

namespace NumberField.StandardAddChar

theorem trace_rat_apply (x : ℚ) : Algebra.trace ℚ ℚ x = x := by
  have h := Algebra.trace_algebraMap (R := ℚ) (S := ℚ) x
  rw [Module.finrank_self, one_smul] at h
  rw [show algebraMap ℚ ℚ x = x from by
    rw [eq_ratCast (algebraMap ℚ ℚ) x, Rat.cast_id]] at h
  exact h

variable (F : Type) [Field F] [NumberField F]


namespace AdelicTraceData

variable {F}
variable (T : AdelicTraceData F)

def adelicTrace : AdeleRing (𝓞 F) F →+ AdeleRing (𝓞 ℚ) ℚ :=
  AddMonoidHom.prodMap T.traceInf T.traceFin

theorem adelicTrace_apply (u : AdeleRing (𝓞 F) F) :
    T.adelicTrace u = (T.traceInf u.1, T.traceFin u.2) := rfl

theorem adelicTrace_algebraMap (x : F) :
    T.adelicTrace (algebraMap F (AdeleRing (𝓞 F) F) x)
      = algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (Algebra.trace ℚ F x) := by
  refine Prod.ext ?_ ?_
  · exact T.traceInf_algebraMap x
  · exact T.traceFin_algebraMap x

theorem continuous_adelicTrace : Continuous T.adelicTrace :=
  T.continuous_traceInf.prodMap T.continuous_traceFin

def psiK : AddChar (AdeleRing (𝓞 F) F) ℂ :=
  psiQ.compAddMonoidHom T.adelicTrace

theorem psiK_apply (u : AdeleRing (𝓞 F) F) : T.psiK u = psiQ (T.adelicTrace u) := rfl

theorem psiK_algebraMap (x : F) : T.psiK (algebraMap F (AdeleRing (𝓞 F) F) x) = 1 := by
  rw [psiK_apply, adelicTrace_algebraMap]
  exact psiQ_algebraMap (Algebra.trace ℚ F x)

theorem continuous_psiK : Continuous T.psiK :=
  continuous_psiQ.comp T.continuous_adelicTrace

theorem psiK_ne_one : T.psiK ≠ 1 := by
  sorry

theorem isGlobalAddChar_psiK : IsGlobalAddChar F T.psiK where
  principalInvariant := T.psiK_algebraMap
  continuous := T.continuous_psiK
  nontrivial := T.psiK_ne_one

end AdelicTraceData

def ratTraceData : AdelicTraceData ℚ where
  traceFin := AddMonoidHom.id _
  traceInf := AddMonoidHom.id _
  traceFin_algebraMap x := by
    rw [AddMonoidHom.id_apply]; congr 1; exact (trace_rat_apply x).symm
  traceInf_algebraMap x := by
    rw [AddMonoidHom.id_apply]; congr 1; exact (trace_rat_apply x).symm
  continuous_traceFin := continuous_id
  continuous_traceInf := continuous_id
  traceInf_surjective := Function.surjective_id

theorem ratTraceData_psiK : ratTraceData.psiK = psiQ := by
  ext u
  rfl

end NumberField.StandardAddChar

end
