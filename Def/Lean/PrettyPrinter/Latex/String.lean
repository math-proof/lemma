module

public import Def.Data.String.String.Part2

@[expose] public section

set_option linter.unusedVariables false


/-- Inner text of a `«…»` name, when the whole string is quoted. -/
def String.guillemetInner? (s : String) : Option String :=
  if s.startsWith "«" && s.endsWith "»" then
    some ((s.drop 1).dropEnd 1).toString
  else
    none

/-- Body of `\sf{w}` (one backslash). `none` when `s` is not that form. -/
def String.sfBody? (s : String) : Option String :=
  let p := "\\sf{"
  if s.startsWith p && s.endsWith "}" then
    let body := ((s.drop p.length).dropEnd 1).toString
    if body.isEmpty then none else some body
  else
    none

/-- `«\sf{x}»` (`Name.toString` of an observed value). -/
def String.isObservedName (s : String) : Bool :=
  match s.guillemetInner? with
  | some inner => inner.endsWith ".bvar" || inner.sfBody?.isSome
  | none => false

/-- Match key against the random variable: `«\sf{x}»` → `x`. -/
def String.bvarKey (s : String) : String :=
  match s.guillemetInner? with
  | some inner =>
    if inner.endsWith ".bvar" then
      (inner.dropEnd ".bvar".length).toString
    else
      inner.sfBody?.getD s
  | none => s

/-- Display form of a guillemet / observed name.

`«\sf{x}»` is the LaTeX `\sf{x}` (already escaped; do not run `escape_specials`
on it). The random variable `x` itself is rendered red elsewhere; this observed
value stays black.

Other guillemet identifiers (e.g. `«λ_1»`, `«λ_{{^\#}1}»`) strip `«»` and keep
the inner text as LaTeX — including embedded commands — so KaTeX is not handed
raw guillemets. -/
def String.bvarLatex (s : String) : String :=
  match s.guillemetInner? with
  | some inner =>
    if inner.endsWith ".bvar" then
      (inner.dropEnd ".bvar".length).toString
    else if inner.sfBody?.isSome then
      inner
    else
      -- Latex-embedded id: strip guillemets; do not keep `«…»` in the math string.
      inner
  | none => s

/-- `escape_specials` after `bvarLatex`. `\sf{w}` and other embedded LaTeX
(backslash commands inside guillemet ids) keep their backslashes and braces. -/
def String.escapeBvarLatex (s : String) : String :=
  if s.sfBody?.isSome || s.contains '\\' then s else s.escape_specials
