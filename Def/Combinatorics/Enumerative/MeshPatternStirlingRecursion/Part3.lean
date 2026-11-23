/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean -/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.MeshPatternStirlingRecursion

@[expose] public section

section

namespace MetaMathlibExt

/-- `Phi` as an equivalence, by injectivity plus a cardinality count. -/
noncomputable def PhiEquiv (m : ℕ) :
    Fin (m.succ) × Equiv.Perm (Fin m) ≃ Equiv.Perm (Fin (m.succ)) :=
  Equiv.ofBijective _ (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨Phi_injective m, ?_⟩
    rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin,
      Fintype.card_perm, Fintype.card_fin, Fintype.card_fin,
      Nat.succ_eq_add_one, Nat.factorial_succ])

end MetaMathlibExt
end
