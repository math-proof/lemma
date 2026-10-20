import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry7Example1Boundary
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry7Example1Boundary


/--
[ramanujan_part1_ch2_entry7_example1_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example1Boundary.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry7_example1_boundary_eq
  :
-- imply
  HasSum (fun k : ℕ => Real.arctan ((2 : ℝ) / (((Real.sqrt 5 - 1) / 2 + ((k : ℝ) + 1)) ^ 2)))
    (Real.pi / 2) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example1Boundary.ramanujan_part1_ch2_entry7_example1_boundary


-- created on 2026-10-20
