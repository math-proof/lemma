import Lemma.AutomorphicForm.ArchDerivCasimir
import Inductive.AutomorphicForm_ArchDirComplex
import Def.AutomorphicForm_ArchDerivCasimirComplex

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

open NumberField NumberField.InfinitePlace.Completion Matrix Complex

variable (F : Type) [Field F] [NumberField F]

section ComplexPlaceTransport

variable {F}


theorem archComplexLiftAt_of_det_ne_zero {w : InfinitePlace F} (hw : w.IsComplex) {e : Fin 2 → Fin 2 → ℂ}
    (h : (Matrix.of e).det ≠ 0) :
    archComplexLiftAt hw e = archComplexGLAt hw (GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h) :=
  dif_pos h

theorem isOpen_setOf_det_ne_zero_complex :
    IsOpen {e : Fin 2 → Fin 2 → ℂ | (Matrix.of e).det ≠ 0} :=
  (isClosed_singleton.preimage (continuous_id.matrix_det)).isOpen_compl


theorem isArchSmoothAtComplex_const {w : InfinitePlace F} (hw : w.IsComplex) (c : ℂ) :
    IsArchSmoothAtComplex hw (fun _ => c) :=
  fun _ => contDiffOn_const

end ComplexPlaceTransport

section ComplexFlows

variable {F}


theorem splitTorusGL2Complex_zero : splitTorusGL2Complex 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitTorusGL2Complex]

theorem splitTorusGL2Complex_add (z z' : ℂ) : splitTorusGL2Complex (z + z') = splitTorusGL2Complex z * splitTorusGL2Complex z' := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [splitTorusGL2Complex, Matrix.mul_apply, Fin.sum_univ_two, Complex.exp_add]; ring_nf


theorem archFlowMatrixComplex_zero (d : ArchDirComplex) : archFlowMatrixComplex d 0 = 1 := by
  cases d
  · simpa [archFlowMatrixComplex] using splitTorusGL2Complex_zero
  · simp [archFlowMatrixComplex, unipotentGL2_zero]
  · simp [archFlowMatrixComplex, lowerUnipotentGL2_zero]
  · simpa [archFlowMatrixComplex] using splitTorusGL2Complex_zero
  · simp [archFlowMatrixComplex, unipotentGL2_zero]
  · simp [archFlowMatrixComplex, lowerUnipotentGL2_zero]

theorem archFlowMatrixComplex_add (d : ArchDirComplex) (s t : ℝ) :
    archFlowMatrixComplex d (s + t) = archFlowMatrixComplex d s * archFlowMatrixComplex d t := by
  cases d
  · simp [archFlowMatrixComplex, ← splitTorusGL2Complex_add]
  · simp [archFlowMatrixComplex, ← unipotentGL2_add]
  · simp [archFlowMatrixComplex, ← lowerUnipotentGL2_add]
  · simp [archFlowMatrixComplex, ← splitTorusGL2Complex_add, add_mul]
  · simp [archFlowMatrixComplex, ← unipotentGL2_add, add_mul]
  · simp [archFlowMatrixComplex, ← lowerUnipotentGL2_add, add_mul]


theorem archFlowAtComplex_zero {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex) : archFlowAtComplex hw d 0 = 1 := by
  rw [archFlowAtComplex, archFlowMatrixComplex_zero, map_one]

theorem archFlowAtComplex_add {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex) (s t : ℝ) :
    archFlowAtComplex hw d (s + t) = archFlowAtComplex hw d s * archFlowAtComplex hw d t := by
  rw [archFlowAtComplex, archFlowMatrixComplex_add, map_mul]; rfl


theorem archDerivAtComplex_const {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex) (c : ℂ) :
    archDerivAtComplex hw d (fun _ => c) = fun _ => 0 := by
  funext g; simp [archDerivAtComplex]

theorem archDelAt_const {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDir) (c : ℂ) :
    archDelAt hw d (fun _ => c) = fun _ => 0 := by
  funext g; simp [archDelAt, archDerivAtComplex_const]

theorem archDelBarAt_const {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDir) (c : ℂ) :
    archDelBarAt hw d (fun _ => c) = fun _ => 0 := by
  funext g; simp [archDelBarAt, archDerivAtComplex_const]

theorem archCasimirAtComplex_const {w : InfinitePlace F} (hw : w.IsComplex) (c : ℂ) :
    archCasimirAtComplex hw (fun _ => c) = fun _ => 0 := by
  funext g
  simp [archCasimirAtComplex, archDelAt_const]

theorem archCasimirBarAtComplex_const {w : InfinitePlace F} (hw : w.IsComplex) (c : ℂ) :
    archCasimirBarAtComplex hw (fun _ => c) = fun _ => 0 := by
  funext g
  simp [archCasimirBarAtComplex, archDelBarAt_const]

end ComplexFlows

section Circle

variable {F}


theorem hasCircleWeightAt_zero {w : InfinitePlace F} (hw : w.IsComplex) (m : ℤ) :
    HasCircleWeightAt hw m (fun _ => (0 : ℂ)) := fun _ _ _ => by simp

end Circle

end AutomorphicForm

end
