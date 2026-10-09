import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {a : ℕ → α} :
-- imply
  (fun i : Fin (n + 1) => a i) = Fin.cons (a 0) fun i : Fin n => a (i + 1) := by
-- proof
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  ·
    simp
  ·
    simp


@[path]
private lemma shift
  {n a : ℕ}
  {f : ℕ → α} :
-- imply
  (fun i : Fin (n + 1) => f (i + a)) = Fin.cons (f a) fun i : Fin n => f (i + 1 + a) := by
-- proof
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  ·
    simp
  ·
    simp


@[path]
private lemma split
  {k l : ℕ}
  {f : ℕ → α} :
-- imply
  (fun i : Fin (k + l) => f i) = Fin.append (fun i : Fin k => f i) (fun i : Fin l => f (i + k)) := by
-- proof
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  ·
    simp
  ·
    simp [Nat.add_comm]


-- created on 2019-10-16
