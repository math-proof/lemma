
def Prod.mapM [Monad m] (f : α → m α') (g : β → m β') : (α × β) → m (α' × β') :=
  fun ⟨a, b⟩ =>
    return ⟨← f a, ← g b⟩
