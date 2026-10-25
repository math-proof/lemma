import Mathlib


/-! Formalizing a proof (the prime case of) Erdos problem \#707 recently proven by Alexeev, ChatGPT, Lean, and Mixon at https://borisalexeev.com/papers/erdos707.html, following Theorem 8 proven on page 5 -/

/-- A perfect difference set is a set where every nonzero element is uniquely representable as a difference of two elements of the set. -/
def IsPerfectDifferenceSet {N: ℕ} (B: Finset (ZMod N)) := ∀ d: ZMod N, d ≠ 0 → ∃! b: B × B, b.1.val - b.2.val = d

def IsPerfectDifferenceSet.map {N: ℕ} (B: Finset (ZMod N)) (p: (B × B) ⊕ Unit) : ZMod N ⊕ B := match p with
| Sum.inl p => if p.1 = p.2 then Sum.inr p.1 else Sum.inl (p.1.val - p.2.val)
| Sum.inr _ => Sum.inl 0

