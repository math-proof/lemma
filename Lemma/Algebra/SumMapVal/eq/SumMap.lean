import stdlib.List.Vector
import Lemma.Basic


@[main]
private lemma main
  [Add β] [Zero β]
  {s : List.Vector α n}
  {f : α → β} :
-- imply
  (s.val.map f).sum = (s.map f).sum :=
-- proof
  rfl


-- created on 2024-07-01
