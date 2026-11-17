module

public import Theorem.Hyperreal.EqSt.of.InfinitesimalSub

public section

open Hyperreal Int ArchimedeanClass


/--
| attributes | lemma |
| :---: | :---: |
| path | Hyperreal.EqSt_0.of.Infinitesimal |
| mt | Hyperreal.NotInfinitesimal.of.NeSt_0 |
-/
@[mt]
public theorem Hyperreal.EqSt_0.of.Infinitesimal
  {x : ℝ*}
-- given
  (h : x → 0) :
-- imply
  stdPart x = 0 :=
-- proof
  EqSt.of.InfinitesimalSub (x := x) (r := 0) (by simpa)


-- created on 2025-12-09
