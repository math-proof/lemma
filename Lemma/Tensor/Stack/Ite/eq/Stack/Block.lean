import sympy.tensor.stack_ite
import sympy.Basic
import Lemma.Tensor.StackIte.eq.Fun


@[path]
private lemma main
  {α : Type*}
  {m : ℕ}
  (s : Fin (m + 1) → ℕ)
  (f : Fin (m + 1) → ℕ → α) :
-- imply
  (fun i : Fin (∑ j, s j) => Tensor.stackIte m s f i) = fun i => f (finSigmaFinEquiv.symm i).1 (finSigmaFinEquiv.symm i).2 := by
-- proof
  exact Tensor.StackIte.eq.Fun m s f


@[path]
private lemma two
  {α : Type*}
  {a b : ℕ}
  (f : Fin a → α)
  (g : Fin b → α) :
-- imply
  (fun i : Fin (a + b) => if h : i.val < a then f ⟨i.val, h⟩ else g ⟨i.val - a, by omega⟩) = Fin.append f g := by
-- proof
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  ·
    simp [Fin.append_left]
  ·
    simp [Fin.append_right]


-- created on 2021-12-30
