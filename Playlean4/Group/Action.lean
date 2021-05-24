
import Playlean4.Group.Basic
import Playlean4.Group.Subgroup

namespace Group

open Group

section

variable (G : Type) (law : G → G → G) [grp : Group G law]

local infixl:70 " * " => id' law
@[appUnexpander id'] def normal.UnexpandGMul : Lean.PrettyPrinter.Unexpander
  | `(id' law $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => grp.one' -- HACK

section

variable {X : Type} (elaw : G → X → X) -- External Law

local infix:70 " • " => id' elaw
@[appUnexpander id'] def unexpandAction : Lean.PrettyPrinter.Unexpander
  | `(id' elaw $x $y) => `($x * $y)
  | _ => throw ()

class Action where
  identity' : ∀ x : X, one • x = x
  compat : ∀ (g g' : G) (x : X), (g * g') • x = g • (g' • x)

end

end

section

variable {G : Type} {law : G → G → G} [grp : Group G law]

local infixl:70 " * " => id' law
@[appUnexpander id'] def unexpandGMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => grp.one' -- HACK
local notation g"⁻¹" => grp.inv g

namespace Action

section

variable {X : Type} {elaw : G → X → X} [action : Action G law elaw]

local infix:70 " • " => id' elaw
@[appUnexpander id'] def unexpandAction : Lean.PrettyPrinter.Unexpander
  | `(id' elaw $x $y) => `($x • $y)
  | _ => throw ()

@[simp]
theorem identity (x : X) : one • x = x := action.identity' x

theorem reverseCompat (g g' : G) (x : X) : g • (g' • x) = (g * g') • x :=
Eq.symm <| action.compat g g' x

end

end Action

end

namespace Action

variable {G : Type} (law : G → G → G) [grp : Group G law]

local infixl:70 " * " => id' law
@[appUnexpander id'] def unexpandGMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => grp.one' -- HACK
local notation g"⁻¹" => grp.inv g

section

variable {X : Type} (elaw : G → X → X) [action : Action G law elaw]

local infix:70 " • " => id' elaw
@[appUnexpander id'] def unexpandAction' : Lean.PrettyPrinter.Unexpander
  | `(id' elaw $x $y) => `($x • $y)
  | _ => throw ()

def isStable (Y : Set X) : Prop := ∀ y : X, y ∈ Y → ∀ g : G, g • y ∈ Y

def orbit (x : X) : Set X := λ y => ∃ g : G, y = g • x

def memOfSelfOrbit (x : X) : x ∈ orbit elaw x := ⟨ one, by simp ⟩

theorem translatorOfMemOfOrbit {x : X} (y : orbit elaw x) : ∃ g : G, y.val = g • x := y.2

theorem orbitIsStable (x : X) : isStable elaw (orbit elaw x) :=
λ y yIn g => match yIn with
  | ⟨ g', h ⟩ =>  ⟨ (g * g'), by rw [h, ← action.compat] ⟩

def stabilizer (x : X) : Set G := λ g => g • x = x

class Transitive where
  singleOrbit : ∀ x y : X, ∃ g : G, y = g • x

end

namespace Remarkable

section

def onSelf : G → G → G := id' law

instance onSelfIsAction : Action G law (@onSelf G law) where
  identity' := λ g => by simp [onSelf]; exact grp.oneNeutralLeft _
  compat := λ g g' g'' => by simp [onSelf]; exact grp.assoc _ _ _

end

variable {X : Type} (elaw : G → X → X) [action : Action G law elaw]

local infix:70 " • " => id' elaw
@[appUnexpander id'] def unexpandAction : Lean.PrettyPrinter.Unexpander
  | `(id' elaw $x $y) => `($x • $y)
  | _ => throw ()

section

def liftToSet : (G → Set X → Set X) :=
  λ (g : G) => Set.img (λ x => g • x)

instance actionOnSet : Action G law (liftToSet elaw) where
  identity' := by
    intro x
    simp [liftToSet]
    funext a
    exact propext ⟨ (λ h => match h with
      | ⟨ y, h ⟩ => by rw [h.2]; simp; exact h.1),
      (λ h => ⟨ a, ⟨ h, by simp ⟩ ⟩) ⟩
  compat := by
    intro g g' x
    simp [liftToSet]
    funext a
    exact propext ⟨
      (λ h => match h with
      | ⟨ y, h ⟩ => ⟨ g' • y, by simp only []; exact
        (action.compat _ _ _) ▸ ⟨ ⟨ y, ⟨ h.1, rfl ⟩ ⟩, h.2 ⟩ ⟩),
      (λ h => match h with
      | ⟨ y₁, ⟨ ⟨ y₂, ⟨ y₂In, (h₁ : y₁ = g' • y₂) ⟩ ⟩, (h₂ : a = g • y₁) ⟩ ⟩ =>
        ⟨ y₂, ⟨ y₂In, by simp only []; exact (action.compat _ _ _).symm ▸ h₁ ▸ h₂ ⟩ ⟩) ⟩

end

section

variable (Y : Set X) (stable : isStable elaw Y)

def restr : G → Y → Y := λ g y => ⟨ g • y.1, stable y.1 y.2 g ⟩

instance restrAction : Action G law (restr elaw Y stable) where
  identity' := by
    intro y
    apply Subtype.eq
    simp [restr, id', show elaw one y = y from action.identity y]
  compat := by
    intro g g' y
    apply Subtype.eq
    simp [restr, id',
      show elaw (law g g') y = elaw g (elaw g' y) from action.compat _ _ _]

end

section

variable (x₀ : X)

def onOrbit : G → orbit elaw x₀ → orbit elaw x₀ :=
  restr elaw (orbit elaw x₀) (orbitIsStable law elaw x₀)

instance onOrbitTransitive : Transitive (onOrbit law elaw x₀) where
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

instance leftTranslationAction (g : G) : Action G law (leftTranslation law) where
  identity' := λ x => by
    simp [id', leftTranslation]
    exact @oneNeutralLeft G law _ _
  compat := λ g g' g'' => by
    simp [id', leftTranslation]
    exact @assoc G law _ _ _ _

def conjugation : G → G → G := λ g g' => g * g' * g⁻¹

instance conjugationAction (g : G) : Action G law (conjugation law) where
  identity' := λ x => by
    suffices one * x * one⁻¹ = x by exact this
    simp
  compat := λ g g' x => by
    suffices ((g * g') * x * (g * g')⁻¹ = g * (g' * x * g'⁻¹) * g⁻¹) by exact this
    simp

end

end Remarkable

end Action

end Group
