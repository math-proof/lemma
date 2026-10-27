import Lean
open Lean


def Array.unshift {α : Type u} (a : Array α) (v : α) : Array α where
  toList := v :: a.toList

def Array.shift (a : Array α) : Array α where
  -- toList := a.toList.drop 1
  toList := match a.toList with
    | [] => []
    | _ :: tail => tail

