
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

@[inline]
def asSubtype {X : Type} (Y : Set X) := Subtype (λ x => x ∈ Y)

instance {X : Type} : CoeSort (Set X) Type where
  coe Y := Subtype (λ x => x ∈ Y)

end Set
