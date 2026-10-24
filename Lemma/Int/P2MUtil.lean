import Mathlib
import Lean

open Lean Elab Tactic Meta in
elab "p2m_exact_reverting " e:term : tactic => do
  let g ← getMainGoal
  let lctx := (← g.getDecl).lctx
  let fvars := lctx.foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc else acc.push d.fvarId
  let (_, g') ← g.revert fvars (preserveOrder := true) (clearAuxDeclsInsteadOfRevert := true)
  g'.withContext do
    let tgt ← g'.getType
    let v ← Term.withSynthesize <| elabTermEnsuringType e tgt
    let v ← instantiateMVars v
    if v.hasExprMVar then throwError "p2m_exact_reverting: unassigned metavariables remain"
    g'.assign v
  replaceMainGoal []

open Lean Elab Command Meta in
elab "#p2m_type_eq " a:ident b:ident : command => liftTermElabM do
  let some ia := (← getEnv).find? a.getId | throwError m!"#p2m_type_eq: unknown constant {a.getId}"
  let some ib := (← getEnv).find? b.getId | throwError m!"#p2m_type_eq: unknown constant {b.getId}"
  let la ← ia.levelParams.mapM fun _ => mkFreshLevelMVar
  let lb ← ib.levelParams.mapM fun _ => mkFreshLevelMVar
  let ta := ia.type.instantiateLevelParams ia.levelParams la
  let tb := ib.type.instantiateLevelParams ib.levelParams lb
  if ← isDefEq ta tb then

    let mut pinned : Array String := #[]
    let mut seen : Array Level := #[]
    for l in la, nm in ia.levelParams do
      let l' ← instantiateLevelMVars l
      match l' with
      | .mvar _ => if seen.contains l' then pinned := pinned.push s!"{nm} (identified with another)" else seen := seen.push l'
      | _ => pinned := pinned.push s!"{nm} := {l'}"
    if pinned.isEmpty then
      logInfo m!"P2M_TYPE_EQ {a.getId} {b.getId}"
    else
      throwError m!"P2M_UNDERGENERAL: the statement's universes {pinned} had to be specialised to match the proof — the proof is less general than the card"
  else
    throwError m!"P2M_TYPE_MISMATCH\n  {a.getId} : {ta}\n  {b.getId} : {tb}"

open Lean Elab Command in
elab "p2m_ns " s:str : command => modifyEnv fun env => env.registerNamespace s.getString.toName
open Lean Elab Command in
def p2mOpenCore (s : String) : CommandElabM Unit := do
  for w in s.splitOn " " do
    if w.isEmpty then continue

    let parts := w.splitOn "~"
    let ns := parts.head!.toName
    let hidden := (parts.drop 1).filter (· ≠ "") |>.map (fun h => h.toName)
    modifyScope fun sc => { sc with openDecls := OpenDecl.simple ns hidden :: sc.openDecls }
    activateScoped ns
open Lean Elab Command in
elab "p2m_open " s:str : command => p2mOpenCore s.getString

open Lean Elab Command in
elab "p2m_export_all " n:str s:str : command => do
  let env ← getEnv
  let short := s.getString.toName
  let base := n.getString.toName ++ short
  let cur ← getCurrNamespace
  let mut al : Array (Name × Name) := #[]
  for (c, _) in env.constants.map₂.toList do
    let u := (privateToUserName? c).getD c
    if base.isPrefixOf u && u != base && !u.isInternalDetail then
      al := al.push (cur ++ short ++ u.replacePrefix base Name.anonymous, c)
  modifyEnv fun env => al.foldl (fun env p => addAlias env p.1 p.2) env

open Lean Elab Command Meta in
elab "#p2m_type_eq_warn " a:ident b:ident : command => liftTermElabM do
  let some ia := (← getEnv).find? a.getId | throwError m!"#p2m_type_eq_warn: unknown constant {a.getId}"
  let some ib := (← getEnv).find? b.getId | throwError m!"#p2m_type_eq_warn: unknown constant {b.getId}"
  let la ← ia.levelParams.mapM fun _ => mkFreshLevelMVar
  let lb ← ib.levelParams.mapM fun _ => mkFreshLevelMVar
  let ta := ia.type.instantiateLevelParams ia.levelParams la
  let tb := ib.type.instantiateLevelParams ib.levelParams lb
  if ← isDefEq ta tb then logInfo m!"P2M_TYPE_EQ {a.getId} {b.getId}"
  else logWarning m!"P2M_DUP_TYPE_MISMATCH (non-fatal)\n  {a.getId} : {ta}\n  {b.getId} : {tb}"

open Lean Elab Command in
elab "p2m_alias " a:str n:str : command => do
  let env ← getEnv
  let full := n.getString.toName
  let tgt := if env.contains full then some full else (let p := mkPrivateName env full; if env.contains p then some p else none)
  match tgt with
  | some t => modifyEnv fun env => addAlias env a.getString.toName t
  | none => pure ()

open Lean Elab Command in
elab "p2m_open_scoped " s:str : command => do
  for w in s.getString.splitOn " " do
    if w.isEmpty then continue
    activateScoped ((w.splitOn "~").head!).toName
syntax (name := p2mOpenIn) "p2m_open " str " in" ppLine command : command
open Lean in
macro_rules | `(p2m_open $s:str in $c:command) => return mkNullNode #[← `(section), ← `(p2m_open $s:str), c, ← `(end)]
open Lean Elab Command in
elab "p2m_export " n:str m:str : command => do
  let env ← getEnv
  let ns := n.getString.toName
  let cur ← getCurrNamespace
  let mut al : Array (Name × Name) := #[]
  for w in m.getString.splitOn " " do
    if w.isEmpty then continue
    let full := ns ++ w.toName
    if env.contains full then al := al.push (cur ++ w.toName, full)
    else
      let prv := mkPrivateName env full
      if env.contains prv then al := al.push (cur ++ w.toName, prv)
  modifyEnv fun env => al.foldl (fun env p => addAlias env p.1 p.2) env

open Lean Elab Command in
elab "p2m_reactivate " s:str : command => do
  for w in s.getString.splitOn " " do
    if w.isEmpty then continue
    let ns := w.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env

macro "p2m_open_scoped " s:str " in " c:command : command => `(section p2m_open_scoped $s $c end)
