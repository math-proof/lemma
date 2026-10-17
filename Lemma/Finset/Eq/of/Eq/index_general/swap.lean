import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Basic
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : Fin (n + 1) → Fin (n + 1)}
-- given
  (h₀ : Function.Bijective x)
  (i j : Fin (n + 1)) :
-- imply
  Function.invFun (fun k => x (Equiv.swap (Function.invFun x i) (Function.invFun x j) k)) i
    = Function.invFun x j := by
-- proof
  let ix := Function.invFun x i
  let jx := Function.invFun x j
  let y : Fin (n + 1) → Fin (n + 1) := fun k => x (Equiv.swap ix jx k)
  have hR : Function.RightInverse (Function.invFun x) x := Function.rightInverse_invFun h₀.surjective
  have hy : y jx = i := by
    change x (Equiv.swap ix jx jx) = i
    rw [Equiv.swap_apply_right]
    exact hR i
  have hinj : Function.Injective y := by
    intro a b hab
    exact (Equiv.swap ix jx).injective (h₀.injective hab)
  have hinv : Function.invFun y (y jx) = jx := Function.leftInverse_invFun hinj jx
  rw [hy] at hinv
  simpa [y] using hinv


-- created on 2026-10-11
-- updated on 2026-10-17
