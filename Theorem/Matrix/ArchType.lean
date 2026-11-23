module

public import Theorem.Matrix.RowIsometryInvariance
public import Abbrev.AutomorphicForm_ArchType

public noncomputable section

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField AdelicLevel IsDedekindDomain Matrix

open scoped Classical

namespace AutomorphicForm

section MatrixFurniture

variable (F : Type) [Field F]

noncomputable section

public theorem archMatrixPiEquiv_apply (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
    (w : InfinitePlace F) (i j : Fin 2) :
    archMatrixPiEquiv F m w i j = m i j w := rfl


public theorem archMatrixPiEquiv_archMatrixUpdate (w : InfinitePlace F)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) :
    archMatrixPiEquiv F (archMatrixUpdate F w m)
      = Function.update (1 : Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w m :=
  (archMatrixPiEquiv F).apply_symm_apply _


public theorem archMatrixUpdate_apply_self (w : InfinitePlace F)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) (i j : Fin 2) :
    archMatrixUpdate F w m i j w = m i j := by
  have h := archMatrixPiEquiv_archMatrixUpdate F w m
  have hw := congrFun h w
  simp only [Function.update_self] at hw
  exact congrFun (congrFun hw i) j


public theorem archMatrixUpdate_apply_of_ne (w : InfinitePlace F)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) (i j : Fin 2)
    {v : InfinitePlace F} (hvw : v ≠ w) :
    archMatrixUpdate F w m i j v = (1 : Matrix (Fin 2) (Fin 2) v.Completion) i j := by
  have h := archMatrixPiEquiv_archMatrixUpdate F w m
  have hv := congrFun h v
  simp only [Function.update_of_ne hvw, Pi.one_apply] at hv
  exact congrFun (congrFun hv i) j


public theorem archMatrixUpdate_one (w : InfinitePlace F) :
    archMatrixUpdate F w (1 : Matrix (Fin 2) (Fin 2) w.Completion) = 1 := by
  apply (archMatrixPiEquiv F).injective
  rw [archMatrixPiEquiv_archMatrixUpdate, map_one]
  exact Function.update_eq_self_iff.mpr rfl


public theorem archMatrixUpdate_mul (w : InfinitePlace F)
    (a b : Matrix (Fin 2) (Fin 2) w.Completion) :
    archMatrixUpdate F w (a * b) = archMatrixUpdate F w a * archMatrixUpdate F w b := by
  apply (archMatrixPiEquiv F).injective
  rw [archMatrixPiEquiv_archMatrixUpdate, map_mul,
    archMatrixPiEquiv_archMatrixUpdate, archMatrixPiEquiv_archMatrixUpdate]
  funext v
  by_cases hv : v = w
  · subst hv
    simp
  · simp [Function.update_of_ne hv]


public theorem archComponent_archGLIncl_self (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) :
    archComponent F w (archGLIncl F w k) = k := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show archEval F w (archMatrixUpdate F w (k : _) i j) = (k : _) i j
  rw [archEval_apply, archMatrixUpdate_apply_self]


public theorem archComponent_archGLIncl_of_ne {v w : InfinitePlace F} (hvw : v ≠ w)
    (k : GL (Fin 2) w.Completion) :
    archComponent F v (archGLIncl F w k) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show archEval F v (archMatrixUpdate F w (k : _) i j) = (1 : Matrix (Fin 2) (Fin 2) _) i j
  rw [archEval_apply, archMatrixUpdate_apply_of_ne _ _ _ _ _ hvw]

end ComponentReceipts

section AdelicInclusion

variable (F : Type) [Field F] [NumberField F]

noncomputable section


public theorem glArch_adelicArchGLIncl (k : GL (Fin 2) (InfiniteAdeleRing F)) :
    glArch (𝓞 F) F (adelicArchGLIncl F k) = k := by
  ext i j
  rfl


public theorem glFin_adelicArchGLIncl (k : GL (Fin 2) (InfiniteAdeleRing F)) :
    glFin (𝓞 F) F (adelicArchGLIncl F k) = 1 := by
  ext i j
  rfl

end

end AdelicInclusion

section Predicate

variable (F : Type) [Field F] [NumberField F]


public theorem hasArchType_zero (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup w.Completion →* ℂˣ) :
    HasArchType F χ (fun _ => 0) := fun _ _ _ => by simp


public theorem hasArchType_const_of_trivial (c : ℂ) :
    HasArchType F (fun _ => 1) (fun _ => c) := fun _ _ _ => (one_mul c).symm


public theorem not_hasArchCharacterAt_one_of_ne_one (w : InfinitePlace F)
    (χ : rowIsometrySubgroup w.Completion →* ℂˣ)
    (k : rowIsometrySubgroup w.Completion) (hχ : χ k ≠ 1) :
    ¬ HasArchCharacterAt F w χ (fun _ => (1 : ℂ)) := fun h => by
  have hk := h k 1
  simp only [mul_one] at hk
  exact hχ (Units.val_eq_one.mp hk.symm)


public theorem not_hasArchType_const_of_exists_ne_one
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup w.Completion →* ℂˣ)
    (w₀ : InfinitePlace F) (k : rowIsometrySubgroup w₀.Completion) (hχ : χ w₀ k ≠ 1)
    (c : ℂ) (hc : c ≠ 0) :
    ¬ HasArchType F χ (fun _ => c) := fun h => by
  have hk : c = (χ w₀ k : ℂ) * c := h w₀ k 1
  have : ((χ w₀ k : ℂ) - 1) * c = 0 := by linear_combination -hk
  rcases mul_eq_zero.mp this with h1 | h0
  · exact hχ (Units.val_eq_one.mp (sub_eq_zero.mp h1))
  · exact hc h0

end Predicate

end AutomorphicForm
