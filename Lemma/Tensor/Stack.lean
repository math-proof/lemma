import sympy.Basic


@[path]
private lemma doit.inner
  {n : ℕ}
  {x : Fin 2 → Fin n → α} :
-- imply
  (fun (j : Fin n) (i : Fin 2) => x i j) = fun j => (Fin.cons (x 0 j) (Fin.cons (x 1 j) finZeroElim) : Fin 2 → α) := by
-- proof
  funext j i
  fin_cases i <;> rfl


@[path]
private lemma limits.swap.subst
  [Mul α]
  {n : ℕ}
  {h : Fin n → α}
  {g : Fin n → Fin n → α} :
-- imply
  (fun (j i : Fin n) => h i * g i j) = fun (i j : Fin n) => h j * g j i :=
-- proof
  rfl


@[path]
private lemma limits.subst.offset
  {a b d : ℤ}
  {f : ℤ → α} :
-- imply
  (fun i : Fin (b - a).toNat => f (a + i)) = fun i : Fin (b - a).toNat => f (a + d + i - d) := by
-- proof
  funext i
  congr 1
  ring


-- created on 2026-09-27
