/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/SturmianWord.lean -/


import Def.Combinatorics.InfiniteWord.SturmianWord


namespace MetaMathlibExt

example : factorOnes (fun _ => false) 7 0 = 0 := by simp [factorOnes]

example : factorOnes (fun _ => true) 5 4 = 4 := by simp [factorOnes]

example : IsBalanced (fun _ => false) := by
  have hzero : ∀ i n, factorOnes (fun _ => false) i n = 0 := by
    intro i n
    induction n with
    | zero => rfl
    | succ n ih => simp [factorOnes, ih]
  simp [IsBalanced, hzero]

example : IsBalanced (fun _ => true) := by
  have hone : ∀ i n, factorOnes (fun _ => true) i n = n := by
    intro i n
    induction n with
    | zero => rfl
    | succ n ih => simp [factorOnes, ih]
  simp [IsBalanced, hone]

example : ¬ IsAperiodic (fun _ => false) := by
  intro h
  apply h
  exact ⟨1, 0, Nat.zero_lt_succ 0, fun _ _ => rfl⟩

example (x : ℕ → Bool) (ha : IsAperiodic x) (hb : IsBalanced x) : IsSturmian x :=
  ⟨ha, hb⟩

example (x : ℕ → Bool) (h : IsSturmian x) : IsAperiodic x := h.1

example (x : ℕ → Bool) (h : IsSturmian x) : IsBalanced x := h.2

#print axioms factorOnes
#print axioms IsBalanced
#print axioms IsAperiodic
#print axioms IsSturmian

end MetaMathlibExt
