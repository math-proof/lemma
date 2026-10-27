import Initialize.Lean.Meta.CtorName


#eval mkCtorName ``Lean.Level

def Lean.Level.toString : Level → String
  | zero =>
    "Prop"
  | succ  n =>
    if n == 0 then
      "Type"
    else
      s!"Type {n}"
  | max u v =>
    s!"Sort (max {u} {v})"
  | imax u v =>
    s!"Sort (imax {u} {v})"
  | param name =>
    s!"Sort {name}"
  | mvar id  =>
    s!"{id.name}"

