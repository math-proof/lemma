import Lemma.AutomorphicForm.RowIsometryInvariance

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField AdelicLevel IsDedekindDomain Matrix

open scoped Classical

namespace AutomorphicForm

section MatrixFurniture

variable (F : Type) [Field F]

noncomputable section

abbrev archMatrixPiEquiv :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) ≃+* Π w : InfinitePlace F,
      Matrix (Fin 2) (Fin 2) w.Completion :=
  Matrix.piRingEquiv (β := fun w : InfinitePlace F => w.Completion)

end

end MatrixFurniture

section ComponentReceipts

variable (F : Type) [Field F]

end ComponentReceipts

section AdelicInclusion

variable (F : Type) [Field F] [NumberField F]

noncomputable section

end

end AdelicInclusion

section Predicate

variable (F : Type) [Field F] [NumberField F]

end Predicate

end AutomorphicForm
