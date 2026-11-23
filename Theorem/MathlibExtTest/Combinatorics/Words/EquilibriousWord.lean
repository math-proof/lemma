/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Words/EquilibriousWord.lean -/
module

public import Instance.Combinatorics.Words.EquilibriousWord
public import Theorem.Finset.Words.EquilibriousWord
open MetaMathlibExt

public section

example : IsEquilibriousWord [] := by decide

example : ¬ IsEquilibriousWord [(0 : Fin 2)] := by decide

example : IsEquilibriousWord [(0 : Fin 2), 1] := by decide

example : ¬ IsEquilibriousWord [(0 : Fin 2), 0, 1] := by decide

example : IsEquilibriousWord ([(0 : Fin 2), 1].reverse) := by decide

example : IsEquilibriousWord ([(0 : Fin 2), 1].reverse) ↔
    IsEquilibriousWord [(0 : Fin 2), 1] :=
  isEquilibriousWord_reverse

