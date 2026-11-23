module

public import Def.Lean.Level
public import Def.Lean.Name
public import Def.Lean.Expr.Part11
public import Def.Data.List.List.Basic

@[expose] public section

set_option linter.unusedVariables false


/--
| index |   hex  | color|
| ----- | ------ | -----|
| 0     |"#999"| Gray |
| 1     |"#99f"| Blue |
| 2     |"#9f9"|Green |
| 3     |"#9ff"| Cyan |
| 4     |"#f99"| Red  |
| 5     |"#f9f"| Pink |
| 6     |"#ff9"|Yellow|
| 7     |"#fff"|White |
-/
def Nat.toColor (n : ℕ) (ignore : Bool) : String :=
  if ignore then
    "%s"
  else
    let n := (n + 1) &&& 7
    let b := ['9', 'f'][n &&& 1]!
    let n := n >>> 1
    let g := ['9', 'f'][n &&& 1]!
    let n := n >>> 1
    let r := ['9', 'f'][n &&& 1]!
    -- for katex
    -- s!"\\colorbox\u007b#{r}{g}{b}\u007d\u007b$\\left(%s\\right)$\u007d"
    -- for complex math
    s!"\\colorbox\u007b#{r}{g}{b}\u007d\u007b$\\mathord\u007b\\left(%s\\right)\u007d$\u007d"
    -- for mathjax
    -- s!"\\bbox[#{r}{g}{b}]\u007b\\left(%s\\right)\u007d"
