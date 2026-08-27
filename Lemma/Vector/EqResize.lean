import Lemma.Vector.GetResize.eq.Ite_Get_Mod
open Vector


@[main]
private lemma main
  [Zero α]
-- given
  (v : List.Vector α n) :
-- imply
  v.resize n = v := by
-- proof
  cases n with
  | zero =>
    apply Subsingleton.elim
  | succ n =>
    ext i
    rw [GetResize.eq.Ite_Get_Mod.fin]
    split_ifs with h
    ·
      simp [Nat.mod_eq_of_lt i.isLt]
    ·
      have hi := i.isLt
      simp [Nat.div_self (Nat.succ_pos n)] at h
      omega


-- created on 2026-07-15
-- updated on 2026-08-24
