import sympy.tensor.stack_ite
import sympy.Basic
import Lemma.Tensor.EqStackIte.of.Lt
open Tensor


/-- n-block form: the piecewise stack equals the block concatenation (`finSigmaFinEquiv`). -/
@[path]
private lemma main
-- given
  (m : ℕ)
  (s : Fin (m + 1) → ℕ)
  (f : Fin (m + 1) → ℕ → α) :
-- imply
  (fun i : Fin (∑ j, s j) => Tensor.stackIte m s f i) =
      fun i => f (finSigmaFinEquiv.symm i).1 (finSigmaFinEquiv.symm i).2 := by
-- proof
  funext i
  obtain ⟨p, rfl⟩ := finSigmaFinEquiv.surjective i
  rw [Equiv.symm_apply_apply, finSigmaFinEquiv_apply]
  exact EqStackIte.of.Lt m s f p.1 p.2 p.2.2


-- created on 2026-10-07
