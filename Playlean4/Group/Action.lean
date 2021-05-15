
import Playlean4.Group.Basic
import Playlean4.Group.Subgroup

namespace Group

open Group

section

variable (G : Magma) [h : Group G]

local infixl:70 " * " => id' Magma.law G
@[appUnexpander id'] def normal.UnexpandGMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => h.one' -- HACK

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

end

variable {G : Magma} [grp : Group G]

local infixl:70 " * " => id' Magma.law G
@[appUnexpander id'] def unexpandGMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => grp.one' -- HACK

namespace Action

section

variable {X : Type} {law : G → X → X} [action : Action G law]

local infix:70 " • " => id' law
@[appUnexpander id'] def unexpandAction : Lean.PrettyPrinter.Unexpander
  | `(id' law $x $y) => `($x • $y)
  | _ => throw ()

@[simp]
theorem identity (x : X) : one • x = x := action.identity' x

theorem reverseCompat (g g' : G) (x : X) : g • (g' • x) = (g * g') • x :=
Eq.symm <| action.compat g g' x

end

section

variable {X : Type} (law : G → X → X) [action : Action G law]

local infix:70 " • " => id' law
@[appUnexpander id'] def unexpandAction' : Lean.PrettyPrinter.Unexpander
  | `(id' law $x $y) => `($x • $y)
  | _ => throw ()

def isStable (Y : Set X) : Prop := ∀ y : X, y ∈ Y → ∀ g : G, id' law g y ∈ Y

def orbit (x : X) : Set X := λ y => ∃ g : G, y = g • x

def memOfSelfOrbit (x : X) : x ∈ orbit law x := ⟨ one, by simp ⟩

#print memOfSelfOrbit

theorem orbitIsStable (x : X) : isStable law (orbit law x) :=
λ y yIn g => match yIn with
  | ⟨ g', h ⟩ =>  ⟨ (g * g'), by rw [h, ← action.compat] ⟩

def stabilizer (x : X) : Set G := λ g => g • x = x

class Transitive where
  singleOrbit : ∀ x y : X, ∃ g : G, y = g • x

end

namespace Remarkable

section

def onSelf : G → G → G := Magma.law G

instance onSelfIsAction : Action G onSelf where
  identity' := λ g => by simp [onSelf]; exact grp.oneNeutralLeft _
  compat := λ g g' g'' => by simp [onSelf]; exact grp.assoc _ _ _

end

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

variable (Y : Set X) (stable : isStable law Y)

def restr : G → Y → Y := λ g y => ⟨ g • y.1, stable y.1 y.2 g ⟩

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

section

variable (x₀ : X)

def onOrbit : G → orbit law x₀ → orbit law x₀ :=
  restr law (orbit law x₀) (orbitIsStable law x₀)

--instance onOrbitAction : Action G (onOrbit law x₀) :=
--  restrAction law (orbit law x₀) (orbitIsStable law x₀)

instance onOrbitTransitive : Transitive (onOrbit law x₀) where
  singleOrbit := by
    intro ⟨ x, xIn ⟩ ⟨ y, yIn ⟩
    match xIn, yIn with
    | ⟨ g₁, xIs ⟩, ⟨ g₂, yIs ⟩ =>
      suffices p₂ : y = (g₂ * g₁⁻¹) • x
      from ⟨ (g₂ * g₁⁻¹), Subtype.eq p₂ ⟩
      simp [xIs, yIs, action.reverseCompat]

end

section

def leftTranslation : G → G → G := λ g g' => g * g'

instance leftTranslationAction (g : G) : Action G leftTranslation where
  identity' := λ x => by
    simp [id', leftTranslation]
    exact @oneNeutralLeft G _ _
  compat := λ g g' g'' => by
    simp [id', leftTranslation]
    exact @assoc G _ _ _ _

end

end Remarkable

end Action

end Group
