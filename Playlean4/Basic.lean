
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

def img {X Y : Type} (f : X → Y) (P : Set X) : Set Y :=
  λ y => ∃ x, x ∈ P ∧ y = f x

def imgComp {X Y Z : Type} {f : X → Y} {g : Y → Z} {P : Set X} :
  img g (img f P) = img (g ∘ f) P :=
by
  funext z
  apply propext
  simp [img, Function.comp]
  exact ⟨ λ h => match h with
    | ⟨ y, ⟨ ⟨ x, ⟨ xIn, xImg ⟩ ⟩, yImg ⟩ ⟩ =>
      ⟨ x, ⟨ xIn, xImg ▸ yImg ▸ rfl ⟩ ⟩,
    λ h => match h with
    | ⟨ x, ⟨ xIn, xImg ⟩ ⟩ =>
      ⟨ (f x), ⟨ ⟨ x, ⟨ xIn, rfl ⟩ ⟩, xImg ⟩ ⟩ ⟩

def imgCongrFun {X Y : Type} {f g : X → Y} {P : Set X} (h : f = g) :
  img f P = img g P := by rw [h]

end Set
