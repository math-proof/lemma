import Def.Data.List.Slice
import Macro.Data.List.List.Part8
open Lean


def List.enumerate (s : List α) : List (Fin s.length × α) :=
  List.range s.length |>.pmap
    (
      fun i hi =>
        let i : Fin s.length := ⟨i, (List.mem_range (n := s.length) (m := i)).mp hi⟩
        ⟨i, s[i]⟩
    )
    (by simp)

def List.permute (s : List α) (i : Fin s.length) (d : ℤ) : List α :=
  match d with
  | .ofNat d =>
    let d := d.succ
    -- s[:i] ++ [s[i]] ++ s[i + 1:i + d] ++ s[i + d:], transform to:
    -- s[:i] ++ s[i + 1:i + d] ++ [s[i]] ++ s[i + d:]
    s.take i ++ s.slice (i + 1) (i + d) ++ s[i] :: s.drop (i + d)
  | .negSucc d =>
    -- s[:i - d] ++ s[i - d:i] ++ [s[i]] ++ s[i + 1:], transform to:
    -- s[:i - d] ++ [s[i]] ++ s[i - d:i] ++ s[i + 1:]
    let d := d.succ
    s.take (i - d) ++ s[i] :: s.slice (i - d) i ++ s.drop (i + 1)

