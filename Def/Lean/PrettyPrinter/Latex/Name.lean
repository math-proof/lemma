module

public import Def.Lean.Name
public import Def.Lean.PrettyPrinter.Latex.String

@[expose] public section

open Lean (Name)
set_option linter.unusedVariables false


/-- Name-level variant of `String.bvarLatex`. Guillemet names use `bvarLatex`;
other names use `escape_specials`. -/
def Lean.Name.bvarLatex (name : Name) (sep : String) : String :=
  let s := name.toString
  if s.startsWith "«" && s.endsWith "»" then
    s.bvarLatex
  else
    name.escape_specials sep

/-- lean.js token text for RV-head matching: last segment, `«\sf{x}»` → `x`.

The key is the letter, not the display string `\sf{x}`, so the head `x` still
matches the observed value. -/
def rvToken (n : Name) : String :=
  let n := n.eraseMacroScopes
  -- Prefer the full-name key (`«\sf{s}»` is often one Name segment, guillemets included),
  -- then fall back to the last segment (for `Foo.a` / hygienic names).
  let raw := n.toString
  let key := raw.bvarKey
  if key != raw then key
  else n.getLast.toString.bvarKey

/-- Name key used in RV-head lists (always `mkSimple` of `rvToken`). -/
def rvKey (n : Name) : Name :=
  Name.mkSimple (rvToken n)

/-- Membership by lean.js token text (avoids `Name` equality pitfalls across attr vs Symbol). -/
def rvNamesContain (names : List Name) (n : Name) : Bool :=
  let t := rvToken n
  names.any (fun m => rvToken m == t)
