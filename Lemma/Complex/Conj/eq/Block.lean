import sympy.functions.elementary.complexes
import sympy.Basic
open Complex


@[main]
private lemma main
  {A B C D : Matrix (Fin n) (Fin n) ℂ} :
-- imply
  (Matrix.fromBlocks A B C D).map (fun z => ~z) = Matrix.fromBlocks (A.map (fun z => ~z)) (B.map (fun z => ~z)) (C.map (fun z => ~z)) (D.map (fun z => ~z)) :=
-- proof
  Matrix.fromBlocks_map _ _ _ _ _


-- created on 2026-09-27
