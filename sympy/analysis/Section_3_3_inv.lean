import sympy.analysis.Section_3_3
import Lemma.Set.OneToOne.is.All_Eq

namespace Chapter3

variable [SetTheory]

open SetTheory
open Function

/--
  We cannot use the notation `f⁻¹` for the inverse because in Mathlib's `Inv` class, the inverse
  of `f` must be exactly of the same type of `f`, and `Function Y X` is a different type from
  `Function X Y`.
-/
abbrev Function.inverse {X Y: Set} (f: Function X Y) (h: f.bijective) :
    Function Y X :=
  Function.mk (fun y x ↦ f x = y) (by
    intros
    apply existsUnique_of_exists_of_unique
    · aesop
    intro _ _ hx hx'
    rw [←hx'] at hx
    apply (_root_.Set.OneToOne.is.All_Eq (f := f)).mp h.1
    simp [hx]
  )

end Chapter3
