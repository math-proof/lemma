-- lake env lean sympy/printing/mathlib.lean
import Mathlib
open Lean Meta

def hasStrValLiteral: Expr → Bool
  | .app fn arg =>
    hasStrValLiteral fn || hasStrValLiteral arg
  | .lam _ binderType body _
  | .forallE _ binderType body _ =>
    hasStrValLiteral binderType || hasStrValLiteral body
  | .letE _ type value body _ =>
    hasStrValLiteral type || hasStrValLiteral value || hasStrValLiteral body
  | .lit (.strVal _) =>
    true
  | .mdata _ expr =>
    hasStrValLiteral expr
  | .proj _ _ struct =>
    hasStrValLiteral struct
  | _ =>
    false

-- #eval show MetaM Unit from do
#eval do
  let env ← getEnv
  -- for ⟨name, info⟩ in env.constants.toList |>.take 1 do
  for ⟨name, info⟩ in env.constants.toList do
    if ← isInstance name then
      continue
    let name := name.toString
    if name.containsSubstr "._" ||
      name.startsWith "_private." ||
      (
        let name' := name.dropRightWhile Char.isDigit
        if name' == name then
          false
        else
          name'.endsWith ".proof_" || name'.endsWith ".eq_"
      ) then
      continue

    if info.isThm then
      let type := info.type
      if hasStrValLiteral type then
        continue
      println! s!"{Json.compress (Json.mkObj [("name", name), ("type", (format (← Meta.ppExpr type)).pretty)])}"

  -- let msgs ← Core.getMessageLog
  -- for msg in msgs.toArray do
    -- println! ← msg.data.toString
