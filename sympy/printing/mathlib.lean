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
#eval Meta.MetaM.run' do
  let env ← getEnv
  -- optional strided chunking for parallel runs:
  -- CHUNK_IDX=i NUM_CHUNKS=n lake env lean sympy/printing/mathlib.lean
  let chunkIdx := (← IO.getEnv "CHUNK_IDX").map String.toNat! |>.getD 0
  let numChunks := (← IO.getEnv "NUM_CHUNKS").map String.toNat! |>.getD 1
  let mut list := env.constants.toList
  if numChunks > 1 then
    list := list.zipIdx.filterMap fun (p, i) =>
      if i % numChunks == chunkIdx then some p else none
  -- for ⟨name, info⟩ in list.take 1 do
  for (name, info) in list do
    if ← isInstance name then
      continue
    let name := name.toString
    if name.contains "._" ||
      name.startsWith "_private." ||
      (
        let name' := (name.dropEndWhile Char.isDigit).copy
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
