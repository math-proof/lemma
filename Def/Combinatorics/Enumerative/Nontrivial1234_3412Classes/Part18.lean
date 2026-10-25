/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Relation
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Order.Fin.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorem.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part17


namespace MetaMathlibExt

def ntRepCodes5 : List (List ℕ) :=
  [[0, 1, 2, 3, 4], [0, 1, 2, 4, 3], [0, 1, 3, 2, 4],
    [0, 1, 3, 4, 2], [0, 1, 4, 2, 3], [0, 2, 1, 3, 4],
    [1, 0, 2, 3, 4], [1, 2, 3, 4, 0], [4, 0, 1, 2, 3]]

def ntRepCodes6 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 5, 4], [0, 1, 2, 4, 5, 3],
    [0, 1, 2, 5, 4, 3], [0, 1, 4, 3, 2, 5], [0, 1, 5, 3, 4, 2],
    [0, 2, 1, 3, 5, 4], [0, 3, 2, 1, 4, 5], [1, 0, 2, 4, 3, 5],
    [1, 2, 3, 4, 5, 0], [1, 2, 3, 5, 4, 0], [1, 2, 4, 3, 5, 0],
    [1, 2, 4, 5, 3, 0], [1, 2, 5, 3, 4, 0], [1, 3, 2, 4, 5, 0],
    [2, 1, 3, 4, 5, 0], [2, 3, 4, 5, 1, 0], [5, 0, 1, 2, 3, 4],
    [5, 0, 1, 2, 4, 3], [5, 0, 1, 3, 2, 4], [5, 0, 1, 3, 4, 2],
    [5, 0, 1, 4, 2, 3], [5, 0, 2, 1, 3, 4], [5, 1, 0, 2, 3, 4],
    [5, 1, 2, 3, 4, 0], [5, 4, 0, 1, 2, 3]]

def ntJoin64 (chunks : List ℕ) : ℕ :=
  chunks.foldl (fun acc chunk => (acc <<< 64) + chunk) 0

def ntL5 : ℕ :=
  ntJoin64 [
    0xfffffff8,
    0xfffffffffffffff8,
    0xf07523f5fffff0ff,
    0xfff6fff5f2ff01f4,
    0xff10fffffffffff4,
    0xfffffff6ffffff75,
    0xf3fffff6fffff2f0,
    0xfff4ff23f5f43210,
  ]

def ntD5 : ℕ :=
  ntJoin64 [
    0xfffffff1,
    0xfffffffffffffff0,
    0xf11111f1fffff1ff,
    0xfff1fff2f1ff11f1,
    0xff11fffffffffff2,
    0xfffffff1ffffff02,
    0xf2fffff0fffff2f1,
    0xfff2ff22f0f00000,
  ]

def ntL6 : ℕ :=
  ntJoin64 [
    0xffff,
    0xfffff9ffffffffff,
    0xfffffffff9fc7169,
    0xd3f6ffffffc7ffff,
    0xff7ffff6fcfff8cb,
    0xf5ffe51fffffffff,
    0xfffff5fffffffff7,
    0xffffffff16fd3fff,
    0xfff7ffffffcff1ff,
    0xff5ffe74fdbf5a4e,
    0x51f85221060071c2,
    0x2585821048210420,
    0xf89c708be7ffffff,
    0x8bfffffe1fffe7f8,
    0x522107e2ffc22f87,
    0xfffffe2fffe2f81e,
    0x108be1ffffff81c7,
    0xf8be3fffe1f84224,
    0x07e2fffe2f8422f9,
    0xfe210422f896120b,
    0xe1ffc01489410984,
    0x108841f85a2117e2,
    0xffc2050522304221,
    0x0422f8bff09be1ff,
    0xcc1fffffffffffff,
    0xe1f87ff007e2ffc2,
    0x0ffda2f97fffffe2,
    0xfa3ff08be1ffc41f,
    0xfc45f8be1288c1f9,
    0x3ff107e2ffc22fff,
    0xffffc2200462f89e,
    0x108be1ffc41f8bff,
    0xffc4308041f87ff1,
    0x060071c22ffd82f8,
    0x46210420ffffffff,
    0xe3fffffffde1f8bf,
    0xffffe3ffffff87e2,
    0xfffe0ffc22f87e01,
    0x0422ffffffffe1ff,
    0xfffffd61f8bfffff,
    0xe1f8522407e2ffff,
    0xff85a2f97e2fffe2,
    0xfa3ff0896160841f,
    0xfdc7f8bff083e1ff,
    0xda2f958258422505,
    0x22307e200422ffff,
    0xffa3e1fffe1ffd01,
    0xf8be10a041ffffff,
    0x93e2fffe2ffc82f8,
    0x7e211022f804108b,
    0xe1fffe1f8045f8be,
    0x128841f87ff00482,
    0x10420ffc22f9fe01,
    0x0422ffc45f884120,
    0x8010884108be1088,
    0xc1f84a2104201102,
    0x2104221046210420,
  ]

def ntD6 : ℕ :=
  ntJoin64 [
    0xfffffff1ffffffff,
    0xfffffff0f11111f1,
    0xfffff1fffff1fff2,
    0xf1ff11f1ff11ffff,
    0xfffffff2fffffff1,
    0xffffff02f2fffff0,
    0xfffff2f1fff2ff22,
    0xf0f00000f8133611,
    0x1161161454152922,
    0xf41143f1fffff4ff,
    0xfff9fff2f61356f3,
    0xff86f8fffff5fff4,
    0xf11861f8fffff122,
    0xf4f3fff9f76517f6,
    0xfff4f754f2f44575,
    0xf41417f6ff111518,
    0x81348737f61641f4,
    0xff11161518955663,
    0xf6ff81f4ff18ffff,
    0xfffffff5f6ff11f4,
    0xff11ff27f2fffff5,
    0xf1ff77f8ff85ff52,
    0xf5f52527f1ff49f3,
    0xff86ffffff811114,
    0xf21943f9ff56f4ff,
    0xff611118f2ff4602,
    0x2272ff25f5161811,
    0xfffffff3ffffff09,
    0xf2fffff2fffff3f4,
    0xfff3ff54f8f34373,
    0xfffffff6ffffff25,
    0xf8fffff5f71518f7,
    0xfffff727f2f5fff6,
    0xf1ff78272565ff02,
    0xf2ff33f8ff07f205,
    0x0556070427f63374,
    0xfffff2f7fff8ff28,
    0xf6f88076fffff2f6,
    0xfff4ff28f5f48295,
    0xf15661f6fffaf152,
    0xf5f82345f6ff1124,
    0x3a11ff52f0f34373,
    0xff52f73826339645,
    0x72f55607f3034531,
    0x6083485267050700,
  ]

def ntLabel5 (s : List ℕ) : ℕ := (ntL5 >>> (4 * ntLehmer s)) % 16

def ntDistance5 (s : List ℕ) : ℕ := (ntD5 >>> (4 * ntLehmer s)) % 16

def ntLabel6 (s : List ℕ) : ℕ := (ntL6 >>> (5 * ntLehmer s)) % 32

def ntDistance6 (s : List ℕ) : ℕ := (ntD6 >>> (4 * ntLehmer s)) % 16

def ntClassOk (n m : ℕ) (reps : List (List ℕ))
    (label distance : List ℕ → ℕ) (s : List ℕ) : Bool :=
  let l := label s
  let d := distance s
  (!ntHasPatB (ntQuads n) s || l < m) &&
    (ntNbrs (ntQuads n) s).all (fun t => label t == l) &&
    (l ≥ m || d < 15 && if d = 0 then s == reps.getD l []
      else (ntNbrs (ntQuads n) s).any fun t => distance t + 1 == d)

end MetaMathlibExt
