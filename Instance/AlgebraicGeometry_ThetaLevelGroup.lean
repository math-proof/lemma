-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_ThetaLevelGroup.lean: instance decls only.
import Mathlib
import Lemma.AlgebraicGeometry.ThetaLevelGroup

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace AlgebraicGeometry.ThetaLevel

section Heis

variable {g : ℕ} (δ : Fin g → ℕ) (d : ℕ)

namespace Heis

variable {δ} {d}

instance instMul : Mul (Heis δ d) := ⟨fun z z' => ⟨z.a + z'.a + pair δ d z.k z'.h, z.h + z'.h, z.k + z'.k⟩⟩
instance instOne : One (Heis δ d) := ⟨⟨0, 0, 0⟩⟩
instance instInv : Inv (Heis δ d) := ⟨fun z => ⟨-z.a + pair δ d z.k z.h, -z.h, -z.k⟩⟩

instance instGroup : Group (Heis δ d) where
  mul_assoc z z' z'' := by
    refine Heis.ext ?_ ?_ ?_
    · simp only [mul_a, mul_h, mul_k, pair_add_left, pair_add_right]; abel
    · simp only [mul_h]; abel
    · simp only [mul_k]; abel
  one_mul z := by refine Heis.ext ?_ ?_ ?_ <;> simp [pair_zero_left]
  mul_one z := by refine Heis.ext ?_ ?_ ?_ <;> simp [pair_zero_right]
  inv_mul_cancel z := by
    refine Heis.ext ?_ ?_ ?_
    · simp only [mul_a, inv_a, inv_k, one_a, pair_neg_left]; abel
    · simp only [mul_h, inv_h, one_h, neg_add_cancel]
    · simp only [mul_k, inv_k, one_k, neg_add_cancel]

instance instFintype [NeZero d] [∀ i, NeZero (δ i)] : Fintype (Heis δ d) :=
  Fintype.ofEquiv (ZMod (2 * d) × HH δ × HH δ)
    { toFun := fun p => ⟨p.1, p.2.1, p.2.2⟩, invFun := fun z => ⟨z.a, z.h, z.k⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }

instance instDecidableEq : DecidableEq (Heis δ d) := fun z z' =>
  decidable_of_iff (z.a = z'.a ∧ z.h = z'.h ∧ z.k = z'.k)
    ⟨fun hh => Heis.ext hh.1 hh.2.1 hh.2.2, fun hh => by subst hh; exact ⟨rfl, rfl, rfl⟩⟩

instance Gam.instFinite [NeZero d] [∀ i, NeZero (δ i)] : Finite (Gam δ d) := by
  have : Finite (MulAut (Heis δ d)) :=
    Finite.of_injective (fun γ : MulAut (Heis δ d) => γ.toEquiv)
      (fun _ _ hh => MulEquiv.ext (fun x => congrFun (congrArg (⇑) hh) x))
  infer_instance

instance Gam.instFintype [NeZero d] [∀ i, NeZero (δ i)] : Fintype (Gam δ d) :=
  Fintype.ofFinite _


end Heis


end AlgebraicGeometry.ThetaLevel

end
end
