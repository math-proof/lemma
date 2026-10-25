/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.WellFounded
import Mathlib.Order.Lattice.Nat
import Theorem.GameTheory.SpragueGrundy


namespace MetaMathlibExt.SpragueGrundy

/-- Normal-play P-positions: a position is losing iff every move goes to an N-position. -/
noncomputable def IsP (G : ImpartialGame) : G.Pos → Prop :=
  (wfRel G).fix fun p ih => ∀ q (h : q ∈ G.moves p), ¬ ih q h

/-- Disjoint sum of two impartial games: move in exactly one component. -/
noncomputable def gameSum (G H : ImpartialGame) : ImpartialGame :=
  letI := G.eqDec
  letI := H.eqDec
  { Pos := G.Pos × H.Pos
    eqDec := inferInstance
    moves := fun p =>
      (G.moves p.1).image (fun a => (a, p.2)) ∪
        (H.moves p.2).image (fun b => (p.1, b))
    rank := fun p => G.rank p.1 + H.rank p.2
    rank_lt := by
      intro p q h
      simp only [Finset.mem_union, Finset.mem_image] at h
      cases h with
      | inl h1 =>
        obtain ⟨a', ha', heq⟩ := h1
        change (a', p.2) = q at heq
        subst heq
        exact Nat.add_lt_add_right (G.rank_lt p.1 a' ha') _
      | inr h2 =>
        obtain ⟨b', hb', heq⟩ := h2
        change (p.1, b') = q at heq
        subst heq
        exact Nat.add_lt_add_left (H.rank_lt p.2 b' hb') _
    start := (G.start, H.start) }

/-- A single Nim heap of size `n`: positions `0, …, n`, moves decrease the value. -/
def nimHeap (n : ℕ) : ImpartialGame where
  Pos := Fin (n + 1)
  eqDec := inferInstance
  moves := fun k => Finset.univ.filter (fun j => j.val < k.val)
  rank := fun k => k.val
  rank_lt := by
    intro k j h
    simpa using h
  start := ⟨n, Nat.lt_succ_self n⟩

/-- Contextual normal-play equivalence: `G` and `H` are equivalent when they
are interchangeable as summands, i.e. no added context `K` distinguishes
their starting positions as P-positions. -/
noncomputable def Equiv (G H : ImpartialGame) : Prop :=
  ∀ K : ImpartialGame,
    IsP (gameSum G K) (G.start, K.start) ↔
      IsP (gameSum H K) (H.start, K.start)

end MetaMathlibExt.SpragueGrundy
