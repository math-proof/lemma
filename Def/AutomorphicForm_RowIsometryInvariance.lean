module

public import Theorem.Matrix.WindowedSiegelSet

@[expose] public section

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace AutomorphicForm

namespace WindowedSiegel

open Matrix.AdelicLevel

variable {K : Type*} [NormedField K]

def IsRowIsometry (k : GL (Fin 2) K) : Prop :=
  ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ = 1 ∧
    ∀ x y : K,
      ‖x * (k : Matrix (Fin 2) (Fin 2) K) 0 0 + y * (k : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
        + ‖x * (k : Matrix (Fin 2) (Fin 2) K) 0 1
            + y * (k : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2
      = ‖x‖ ^ 2 + ‖y‖ ^ 2

variable (K)

def rowIsometrySubgroup : Subgroup (GL (Fin 2) K) where
  carrier := {k : GL (Fin 2) K | IsRowIsometry k}
  one_mem' := isRowIsometry_one
  mul_mem' := fun hk hk' => IsRowIsometry.mul hk hk'
  inv_mem' := fun hk => IsRowIsometry.inv hk

variable {K}


end WindowedSiegel

end AutomorphicForm

end
