/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/TernaryAbelianCubeFreeLowerBound.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.Count
import Mathlib.Data.Set.Card
import Mathlib.Data.List.GetD
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic.Ring


namespace MetaMathlibExt

section

noncomputable def ac_cnt (ω : ℕ → Fin 3) (a : Fin 3) (i j : ℕ) : ℕ :=
  ((Finset.Ico i j).filter (fun k => ω k = a)).card

def ac_hImg : Fin 3 → List (Fin 3)
  | 0 => [0, 0, 2, 0, 0, 1]
  | 1 => [2, 1, 1, 0, 0, 1]
  | 2 => [2, 2, 0, 2, 2, 1]

def ac_hAlt : Fin 3 → List (Fin 3)
  | 0 => [0, 0, 2, 0, 0, 1]
  | 1 => [0, 0, 1, 1, 2, 1]
  | 2 => [2, 2, 0, 2, 2, 1]

def ac_img (c : Bool) (a : Fin 3) : List (Fin 3) :=
  if c then ac_hAlt a else ac_hImg a

def ac_delta (n : ℕ) : Fin 3 :=
  if _h : n = 0 then 0
  else (ac_hImg (ac_delta (n / 6))).getD (n % 6) 0
termination_by n
decreasing_by
  apply Nat.div_lt_self
  · omega
  · decide

def ac_omega (b : ℕ → Bool) (n : ℕ) : Fin 3 :=
  (ac_img (b (n / 6)) (ac_delta (n / 6))).getD (n % 6) 0

def ac_pre (u : List (Fin 3)) (r : ℕ) : ℤ × ℤ × ℤ :=
  ((u.take r).count 0, (u.take r).count 1, (u.take r).count 2)

-- images table: true = choice, false = plain
def ac_imgs (choice : Bool) : Fin 3 → List (List (Fin 3))
  | 0 => [ac_hImg 0]
  | 1 => if choice then [ac_hImg 1, ac_hAlt 1] else [ac_hImg 1]
  | 2 => [ac_hImg 2]

-- opts(imgs, α): (α', prefix-vector) with u[r] = α
def ac_opts (choice : Bool) (α : Fin 3) : List (Fin 3 × (ℤ × ℤ × ℤ)) :=
  (List.finRange 3).flatMap (fun α' =>
    (ac_imgs choice α').flatMap (fun u =>
      (List.range 6).filterMap (fun r =>
        if u.getD r 0 = α then some (α', ac_pre u r) else none)))

-- adjugate times vector
def ac_adjMul (v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (11 * v.1 - 7 * v.2.1 - v.2.2,
   -3 * v.1 + 15 * v.2.1 - 3 * v.2.2,
   -2 * v.1 - 2 * v.2.1 + 10 * v.2.2)

-- parent of template under options; none if not divisible
def ac_parent (t : (Fin 3 × Fin 3 × Fin 3 × Fin 3) × ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)))
    (o : (Fin 3 × (ℤ × ℤ × ℤ)) × (Fin 3 × (ℤ × ℤ × ℤ)) ×
         (Fin 3 × (ℤ × ℤ × ℤ)) × (Fin 3 × (ℤ × ℤ × ℤ))) :
    Option ((Fin 3 × Fin 3 × Fin 3 × Fin 3) × ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ))) :=
  let (_α, d) := t
  let d1 := d.1; let d2 := d.2
  let e0 := o.1.2; let e1 := o.2.1.2; let e2 := o.2.2.1.2; let e3 := o.2.2.2.2
  let v1 : ℤ × ℤ × ℤ :=
    (d1.1 - e0.1 + 2 * e1.1 - e2.1, d1.2.1 - e0.2.1 + 2 * e1.2.1 - e2.2.1,
     d1.2.2 - e0.2.2 + 2 * e1.2.2 - e2.2.2)
  let v2 : ℤ × ℤ × ℤ :=
    (d2.1 - e1.1 + 2 * e2.1 - e3.1, d2.2.1 - e1.2.1 + 2 * e2.2.1 - e3.2.1,
     d2.2.2 - e1.2.2 + 2 * e2.2.2 - e3.2.2)
  let w1 := ac_adjMul v1; let w2 := ac_adjMul v2
  if w1.1 % 36 = 0 ∧ w1.2.1 % 36 = 0 ∧ w1.2.2 % 36 = 0 ∧
     w2.1 % 36 = 0 ∧ w2.2.1 % 36 = 0 ∧ w2.2.2 % 36 = 0 then
    some ((o.1.1, o.2.1.1, o.2.2.1.1, o.2.2.2.1),
      ((w1.1 / 36, w1.2.1 / 36, w1.2.2 / 36),
       (w2.1 / 36, w2.2.1 / 36, w2.2.2 / 36)))
  else none

-- all parents of t under choice/plain options
def ac_parents (choice : Bool)
    (t : (Fin 3 × Fin 3 × Fin 3 × Fin 3) × ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ))) :
    List ((Fin 3 × Fin 3 × Fin 3 × Fin 3) × ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ))) :=
  let (α, _) := t
  let o0 := ac_opts choice α.1
  let o1 := ac_opts choice α.2.1
  let o2 := ac_opts choice α.2.2.1
  let o3 := ac_opts choice α.2.2.2
  (o0.flatMap (fun a0 => o1.flatMap (fun a1 => o2.flatMap (fun a2 =>
    o3.filterMap (fun a3 => ac_parent t (a0, a1, a2, a3)))))).eraseDups

end
end MetaMathlibExt
