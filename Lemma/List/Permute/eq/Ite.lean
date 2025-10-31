import stdlib.List
import sympy.Basic


@[main]
private lemma main
-- given
  (s : List α)
  (i : Fin s.length)
  (d : ℤ) :
-- imply
  s.permute i d =
    if d < 0 then
      let d := (-d).toNat
      s.take (i - d) ++ s[i] :: s.slice (i - d) i ++ s.drop (i + 1)
    else
      let d := (d + 1).toNat
      s.take i ++ s.slice (i + 1) (i + d) ++ s[i] :: s.drop (i + d) := by
-- proof
  unfold List.permute
  aesop


-- created on 2025-06-07
