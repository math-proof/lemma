import Lean.Attributes
import Lean.Util.CollectAxioms
open Lean


/--
`@[axioms]` logs the same report as `#print axioms` for the declaration it is applied to.
An empty list is a successful report. Use `@[path, axioms]` on a `private lemma main`.
The name `axiom` is a Lean keyword, so the attribute is `axioms`.

Echo debugging only. `Syntax.Tactic.Echo` imports this module, so `*.echo.lean`
files can use the attribute.
-/
initialize registerBuiltinAttribute {
  name := `axioms
  descr := "Log the axiom dependencies of a declaration, as in #print axioms"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let axioms ← collectAxioms declName
    if axioms.isEmpty then
      logInfo m!"'{declName}' does not depend on any axioms"
    else
      logInfo m!"'{declName}' depends on axioms: {axioms.qsort Name.lt |>.map MessageData.ofConstName |>.toList}"
}
