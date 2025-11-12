import stdlib.SEq
import sympy.Basic
import sympy.Basic'

/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.SEq.is.EqCast.of.Eq |
| comm | Bool.EqCast.is.SEq.of.Eq |
| mp   | Bool.EqCast.of.SEq.Eq |
| mpr  | Bool.SEq.of.EqCast.Eq |
| mp.comm 2 | Bool.Eq_Cast.of.SEq.Eq |
| mpr.comm 1 | Bool.SEq.of.Eq_Cast |
| comm.mp 1 | Bool.SEq.is.Eq_Cast.of.Eq |
-/
-- @[main, comm, mp, mpr, mp.comm 2, mpr.comm 1]
@[main, comm.mp' 1]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n}
  {b : Vector m}
-- given
  (h : n = m) :
-- imply
  a ≃ b ↔ cast (by congr) a = b:= by
-- proof
  simp [SEq]
  aesop

-- private lemma reverse
--   {Vector : α → Sort v}
--   {a : Vector n}
--   {b : Vector m}
-- -- given
--   (h : n = m) :
-- -- imply
--   b ≃ a ↔ b = cast (by congr) a :=
-- -- proof
--   Iff.intro
--     (Bool.Eq_Cast.of.SEq.Eq h) --mp.comm 2
--     (Bool.SEq.of.Eq_Cast (h := h)) -- mpr.comm 1
-- #check Iff.comm.mp
-- created on 2025-07-25
-- updated on 2025-10-04
-- #check Bool.Eq_Cast.of.SEq.Eq
-- #check Bool.SEq.of.Eq_Cast
-- #check Iff.intro
