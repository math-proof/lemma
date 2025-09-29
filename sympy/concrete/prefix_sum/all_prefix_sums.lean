import sympy.Basic

-- define the circled plus operator
class OPlus (α : Type u) where
  oplus : α → α → α
  associative : ∀ x y z : α, oplus (oplus x y) z = oplus x (oplus y z)

infixl:60 "⊕" => OPlus.oplus


-- define the circled times operator
class OTimes (α : Type u) [OPlus α] where
  otimes : α → α → α
  distributive : ∀ a b c : α, otimes (a ⊕ b) c = (otimes a c) ⊕ (otimes b c)

infixl:70 "⊗" => OTimes.otimes


-- define the circled dot operator, the companion operator of ⊗
class ODot (α : Type u) [OPlus α] [OTimes α] where
  odot : α → α → α
  semiassociative : ∀ x y z : α, ((x ⊗ y) ⊗ z) = (x ⊗ (odot y z))
  associative : ∀ x y z : α, odot (odot x y) z = odot x (odot y z)

infixl:65 "⊙" => ODot.odot

-- Define the all-prefix-sums function
def all_prefix_sums [Inhabited α] [OPlus α] (a : List α) (t : α := default) : List α :=
  match a, t with
  | [], _  => []
  | a₀ :: a, sum => (sum ⊕ a₀) :: all_prefix_sums a (sum ⊕ a₀)


class Bullet (α : Type u) [OPlus α] [OTimes α] [ODot α] where
  bullet : α × α → α × α → α × α
  property : ∀ cᵢ c_j : α × α, bullet cᵢ c_j = ⟨cᵢ.fst ⊙ c_j.fst, (cᵢ.snd ⊗ c_j.fst) ⊕ c_j.snd⟩

-- define bullet operator
infixl:65 "•" => Bullet.bullet

-- http://shelf2.library.cmu.edu/Tech/23445461.pdf
