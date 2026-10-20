import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.SmithNormalForm
open Submodule
open MathlibExt.LinearAlgebra.SmithNormalFormWanted


/--
[exists_smith_normal_form_dvd_chain](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/SmithNormalForm.lean)
-/
@[path]
private lemma exists_smith_normal_form_dvd_chain_eq
  [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
  {N : Submodule R M} :
-- imply
  ∃ (n m : ℕ) (hnm : n ≤ m) (bM : Module.Basis (Fin m) R M)
    (bN : Module.Basis (Fin n) R N) (a : Fin n → R),
    (∀ i, (bN i : M) = a i • bM (Fin.castLE hnm i)) ∧
    (∀ i, a i ≠ 0) ∧
    (∀ (i : ℕ) (hi1 : i < n) (hi2 : i + 1 < n), a ⟨i, hi1⟩ ∣ a ⟨i + 1, hi2⟩) := by
-- proof
  apply Submodule.exists_smith_normal_form_dvd_chain N

/--
[smithNormalForm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/SmithNormalForm.lean)
-/
@[path]
private lemma smithNormalForm_eq
  [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
  {N : Submodule R M} :
-- imply
  ∃ (n m : ℕ) (hnm : n ≤ m) (bM : Module.Basis (Fin m) R M)
    (bN : Module.Basis (Fin n) R N) (a : Fin n → R),
    (∀ i, (bN i : M) = a i • bM (Fin.castLE hnm i)) ∧
    (∀ i, a i ≠ 0) ∧
    (∀ (i : ℕ) (hi1 : i < n) (hi2 : i + 1 < n), a ⟨i, hi1⟩ ∣ a ⟨i + 1, hi2⟩) := by
-- proof
  apply MathlibExt.LinearAlgebra.SmithNormalFormWanted.smithNormalForm N


-- created on 2026-10-20
