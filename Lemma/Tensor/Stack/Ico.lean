import sympy.Basic


@[path]
private lemma simp
  {start step k : ℕ}
  {f : ℕ → α} :
-- imply
  (List.range' start k step).map f = (List.range k).map fun i => f (i * step + start) := by
-- proof
  apply List.ext_getElem
  ·
    simp
  ·
    intro i _ _
    simp [List.getElem_range', Nat.add_comm, Nat.mul_comm]


@[path]
private lemma retain.step
  {start step k : ℕ}
  {g : ℕ → α}
-- given
  (h : step > 0) :
-- imply
  (List.range k).map g = (List.range' start k step).map fun i => g ((i - start) / step) := by
-- proof
  apply List.ext_getElem
  ·
    simp
  ·
    intro i _ _
    simp [List.getElem_range', Nat.mul_div_cancel_left i h]


-- created on 2021-12-27
