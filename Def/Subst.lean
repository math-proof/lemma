import Abbrev.Subst
import Syntax.Subst

/-- Infoview: `Subst (fun x y ↦ expr) x₀ y₀` ↦ `Subst (expr | x = x₀ ∧ y = y₀)`; any other
application is shown as `Subst f …`. -/
@[app_unexpander «Subst»]
def Subst.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f $vs*) => do
    -- the delaborated lambda is not yet parenthesized here
    if let `(fun $xs:ident* ↦ $body) := f then
      if xs.size == vs.size then
        let bs ← (xs.zip vs).mapM fun (x, v) => `(substBinding| $x:ident = $v)
        return ← `(Subst ($body | $bs∧*))
    `(Subst $f $vs*)
  | _ => throw ()
