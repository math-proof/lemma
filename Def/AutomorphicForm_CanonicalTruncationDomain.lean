import Lemma.AutomorphicForm.WindowedSiegelSet
import Lemma.AutomorphicForm.CentreCutSiegelSet
import Lemma.NumberField.TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace AutomorphicForm

variable (L : Type) [Field L] [NumberField L]

def IsTruncationDatum (α β : ℝ)
    (d : (ℝ × ℝ × ℝ × ℝ) × Set (AdelicGL2 (𝓞 L) L) × Set (AdelicGL2 (𝓞 L) L)) : Prop :=
  0 < d.1.1 ∧ IsCompact d.2.1 ∧
    d.2.2 ⊆ ⋃ y ∈ d.2.1, (· * y) '' WindowedSiegel.centreCutSiegelSet L d.1.1 d.1.2.1 d.1.2.2.1 d.1.2.2.2 ∧
    d.2.2 ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ∧
    IsFundamentalDomain (globalPoints (𝓞 L) L).range d.2.2
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})

open Classical in

def canonicalTruncationData (α β : ℝ) : (ℝ × ℝ × ℝ × ℝ) × Set (AdelicGL2 (𝓞 L) L) × Set (AdelicGL2 (𝓞 L) L) :=
  if h : ∃ d, IsTruncationDatum L α β d then Classical.choose h else ((0, 0, 0, 0), ∅, ∅)

def canonicalTruncationDomain (α β : ℝ) : Set (AdelicGL2 (𝓞 L) L) :=
  (canonicalTruncationData L α β).2.2

def canonicalTruncationTranslates (α β : ℝ) : Set (AdelicGL2 (𝓞 L) L) :=
  (canonicalTruncationData L α β).2.1

def canonicalTruncationFloor (α β : ℝ) : ℝ :=
  (canonicalTruncationData L α β).1.1

def canonicalTruncationWindow (α β : ℝ) : ℝ :=
  (canonicalTruncationData L α β).1.2.1

def canonicalTruncationLowerCut (α β : ℝ) : ℝ :=
  (canonicalTruncationData L α β).1.2.2.1

def canonicalTruncationUpperCut (α β : ℝ) : ℝ :=
  (canonicalTruncationData L α β).1.2.2.2

theorem canonicalTruncationData_eq_of_exists {α β : ℝ}
    (h : ∃ d, IsTruncationDatum L α β d) : canonicalTruncationData L α β = Classical.choose h := by
  unfold canonicalTruncationData
  exact dif_pos h

theorem canonicalTruncationData_spec {α β : ℝ}
    (h : ∃ d, IsTruncationDatum L α β d) : IsTruncationDatum L α β (canonicalTruncationData L α β) := by
  rw [canonicalTruncationData_eq_of_exists L h]
  exact Classical.choose_spec h

end AutomorphicForm

example (L : Type) [Field L] [NumberField L] (α β : ℝ) : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
  AutomorphicForm.canonicalTruncationDomain L α β

example (L : Type) [Field L] [NumberField L]
    (h : ∃ d, AutomorphicForm.IsTruncationDatum L 1 2 d) :
    AutomorphicForm.canonicalTruncationDomain L 1 2 = (Classical.choose h).2.2 := by
  unfold AutomorphicForm.canonicalTruncationDomain
  rw [AutomorphicForm.canonicalTruncationData_eq_of_exists L h]

end
