import stdlib.List
import Lemma.Basic


@[main]
private lemma main
-- given
  (a : List α)
  (i j : ℕ) :
-- imply
  a.swap i j =
    if i = j then
      a
    else if h_lt : i < j then
      if h_j : j < a.length then
        a.take i ++ a[j] :: a.slice (i + 1) j ++ a[i] :: a.drop (j + 1)
      else
        a
    else if h_i : i < a.length then
      a.take j ++ a[i] :: a.slice (j + 1) i ++ a[j] :: a.drop (i + 1)
    else
      a := by
-- proof
  simp [List.swap]


-- created on 2025-05-17
