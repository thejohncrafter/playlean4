
universes u
def id' {α : Sort u} (a : α) : α := a

def Set (X : Type) := X → Prop

namespace Set

def mem {X : Type} (x : X) (s : Set X) := s x

infix:50 " ∈ " => mem

theorem ext {X : Type} (s₁ s₂ : Set X) (h : ∀ x : X, x ∈ s₁ ↔ x ∈ s₂) : s₁ = s₂ :=
by
  funext x
  exact propext <| h x

end Set
