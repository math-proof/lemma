import Lean
open Lean

def Lean.Environment.moduleComponents (env : Environment) : List Name :=
  match env.mainModule.components with
  | [] => panic! "a lemma file must have a lean library name"
  | _ :: tail => tail

def Lean.Environment.module (env : Environment) : Name :=
  env.moduleComponents.foldl .append default

def Lean.Environment.moduleTokens (env : Environment) : List String :=
  env.moduleComponents.map Name.toString
