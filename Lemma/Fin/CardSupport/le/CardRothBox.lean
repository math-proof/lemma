import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[roth_support_card_le_box](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommSemiring R]
  {P : MvPolynomial (Fin m) R} {r : Fin m → ℕ}
-- given
  (hP : rothDegreeBoundOver P r) :
-- imply
  P.support.card ≤ Fintype.card (RothBox r) := by
-- proof
  classical
  let f : RothMvIndex m → RothBox r := fun i h ↦
    ⟨min (i h) (r h), Nat.lt_succ_iff.mpr (min_le_right _ _)⟩
  have hinj : Set.InjOn f (P.support : Set (RothMvIndex m)) := by
    intro i hi j hj hij
    ext h
    have hihr : i h ≤ r h := hP i hi h
    have hjhr : j h ≤ r h := hP j hj h
    have heq := congrArg (fun z : RothBox r ↦ (z h : ℕ)) hij
    simpa [f, min_eq_left hihr, min_eq_left hjhr] using heq
  calc
    _ = (P.support.image f).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ Fintype.card (RothBox r) := by
      simpa using Finset.card_le_univ (P.support.image f)


-- created on 2026-10-21
