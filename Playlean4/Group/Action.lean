
namespace Group

open Group

section

variable {X : Type} (law : G → X → X)

local infix:70 " • " => id' law
@[appUnexpander id'] def unexpandAction : Lean.PrettyPrinter.Unexpander
  | `(id' law $x $y) => `($x * $y)
  | _ => throw ()

class Action where
  identity' : ∀ x : X, one • x = x
  compat : ∀ (g g' : G) (x : X), (g * g') • x = g • (g' • x)

end

variable {G : Magma} [h : Group G]

local infixl:70 " * " => id' Magma.law G
@[appUnexpander id'] def unexpandGMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => h.one' -- HACK

namespace Action

section

variable {X : Type} {law : G → X → X} [action : Action G law]

local infix:70 " • " => id' law
@[appUnexpander id'] def unexpandAction : Lean.PrettyPrinter.Unexpander
  | `(id' law $x $y) => `($x • $y)
  | _ => throw ()

@[simp]
theorem identity (x : X) : one • x = x := action.identity' x

end

namespace Remarkable

variable {X : Type} (law : G → X → X) [action : Action G law]

local infix:70 " • " => id' law
@[appUnexpander id'] def unexpandAction : Lean.PrettyPrinter.Unexpander
  | `(id' law $x $y) => `($x • $y)
  | _ => throw ()

section

def liftToSet : (G → Set X → Set X) :=
  λ (g : G) (s : Set X) => (λ x : X => ∃ (y : X), (y ∈ s) ∧ (x = g • y) )

--local infix:70 " •• " => id' (liftToSet law)
--@[appUnexpander id'] def unexpandLiftedAction : Lean.PrettyPrinter.Unexpander
--  | `(id' (liftToSet law) $x $y) => `($x •• $y)
--  | _ => throw ()

instance actionOnSet : Action G (liftToSet law) where
  identity' := by
    intro x
    simp [liftToSet]
    funext a
    exact propext ⟨ (λ h => match h with
      | ⟨ y, h ⟩ => by exact h.2 ▸ (action.identity _).symm ▸ h.1),
      (λ h => ⟨ a, ⟨ h, (action.identity _).symm ▸ rfl ⟩ ⟩) ⟩
  compat := by
    intro g g' x
    simp [liftToSet]
    funext a
    exact propext ⟨
      (λ h => match h with
      | ⟨ y, h ⟩ => ⟨ g' • y,
        (action.compat _ _ _) ▸ ⟨ ⟨ y, ⟨ h.1, rfl ⟩ ⟩, h.2 ⟩ ⟩),
      (λ h => match h with
      | ⟨ y₁, ⟨ ⟨ y₂, ⟨ y₂In, h₁ ⟩ ⟩, h₂ ⟩ ⟩ =>
        ⟨ y₂, ⟨ y₂In, (action.compat _ _ _).symm ▸ h₁ ▸ h₂ ⟩ ⟩) ⟩

end

section

variable (Y : Set X) (stable : ∀ y : X, y ∈ Y → ∀ g : G, id' law g y ∈ Y)

def restr (g : G) (y : Subtype Y) : Subtype Y :=
  ⟨ g • y.1, stable y.1 y.2 g ⟩

instance restrAction : Action G (restr law Y stable) where
  identity' := by
    intro y
    apply Subtype.eq
    simp [restr, id', show law one y = y from action.identity y]
  compat := by
    intro g g' y
    apply Subtype.eq
    simp [restr, id',
      show law (G.law g g') y = law g (law g' y) from action.compat _ _ _]

end

end Remarkable

end Action

end
