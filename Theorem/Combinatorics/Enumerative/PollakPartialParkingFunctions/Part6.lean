module
public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Instance.Combinatorics.Enumerative.ParkingFunction
public import Theorem.Finset.Enumerative.ParkingFunction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/
namespace MetaMathlibExt.PollakPartialParking

theorem linFirstFree_mem (t : ℕ) (occ : Finset (Fin t)) (a : ℕ) (x : Fin t)
    (hx : linFirstFree t occ a = some x) : a ≤ x.val ∧ x ∉ occ := by
  unfold linFirstFree at hx
  split_ifs at hx with h
  case pos =>
    have hxeq : (Finset.univ.filter
          (fun k : Fin t => a ≤ k.val ∧ k ∉ occ)).min' h = x :=
          Option.some_inj.mp hx
    have hmem := Finset.min'_mem _ h
    rw [Finset.mem_filter] at hmem
    rw [← hxeq]
    exact hmem.2

theorem linFirstFree_le (t : ℕ) (occ : Finset (Fin t)) (a : ℕ) (x : Fin t)
    (hx : linFirstFree t occ a = some x) (y : Fin t)
    (hy1 : a ≤ y.val) (hy2 : y ∉ occ) : x.val ≤ y.val := by
  unfold linFirstFree at hx
  split_ifs at hx with h
  case pos =>
    have hxeq : (Finset.univ.filter
          (fun k : Fin t => a ≤ k.val ∧ k ∉ occ)).min' h = x :=
          Option.some_inj.mp hx
    subst hxeq
    have hmem : y ∈ Finset.univ.filter (fun k : Fin t => a ≤ k.val ∧ k ∉ occ) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy1, hy2⟩
    have hle := Finset.min'_le _ y hmem
    exact Fin.le_def.mp hle

theorem linFirstFree_none (t : ℕ) (occ : Finset (Fin t)) (a : ℕ)
    (hx : linFirstFree t occ a = none) (y : Fin t) (hy1 : a ≤ y.val) :
    y ∈ occ := by
  unfold linFirstFree at hx
  split_ifs at hx with h
  case neg =>
    by_contra hycon
    apply h
    exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy1, hycon⟩⟩

end MetaMathlibExt.PollakPartialParking
