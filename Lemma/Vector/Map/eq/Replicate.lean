import Lemma.Vector.GetMap.eq.UFnGet
open Vector


@[main]
private lemma main
  {s : List.Vector α n}
  {default : α} :
-- imply
  (s.map fun _ => default) = List.Vector.replicate n default := by
-- proof
  apply List.Vector.ext
  intro i
  simp


-- created on 2024-07-01
