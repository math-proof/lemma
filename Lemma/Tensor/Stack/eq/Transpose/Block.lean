import sympy.Basic
open Matrix


@[main]
private lemma main
  {m k l : ℕ}
  {f : ℕ → ℕ → α} :
-- imply
  (Matrix.of fun (i : Fin m) (j : Fin (k + l)) => f i j) =
    (Matrix.of (Fin.append (fun (j : Fin k) (i : Fin m) => f i j) (fun (j : Fin l) (i : Fin m) => f i (j + k))))ᵀ := by
-- proof
  ext i j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  ·
    simp
  ·
    simp [Nat.add_comm]


-- created on 2019-10-22
