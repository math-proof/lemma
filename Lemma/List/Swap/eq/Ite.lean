import stdlib.List
import sympy.Basic


@[main]
private lemma main
-- given
  (s : List α)
  (i j : ℕ) :
-- imply
  s.swap i j =
    if i = j then
      s
    else if h_lt : i < j then
      if h_j : j < s.length then
        s.take i ++ s[j] :: s.slice (i + 1) j ++ s[i] :: s.drop (j + 1)
      else
        s
    else if h_i : i < s.length then
      s.take j ++ s[i] :: s.slice (j + 1) i ++ s[j] :: s.drop (i + 1)
    else
      s := by
-- proof
  simp [List.swap]


-- created on 2025-05-17
