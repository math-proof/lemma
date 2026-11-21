import Def.Data.Vector.Basic
import Instance.Data.Vector.Vector


@[path]
private lemma main
-- given
  (s : List.Vector α n)
  (a default : α) :
-- imply
  (a ::ᵥ s).headD default = a :=
-- proof
  rfl


-- created on 2024-07-01
-- updated on 2026-11-20
