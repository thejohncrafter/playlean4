
import Playlean4.Basic

set_option quotPrecheck false

structure Magma where
  carrier : Type
  law : carrier → carrier → carrier

section

variable (G : Magma)

instance CoeCarrier : CoeSort Magma Type where
  coe m := m.carrier

local infixl:70 " * " => id' Magma.law G
@[appUnexpander id'] def unexpandMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x * $y)
  | _ => throw ()

class Group where
  one' : G -- Name hack
  assoc : ∀ g₁ g₂ g₃ : G, (g₁ * g₂) * g₃ = g₁ * (g₂ * g₃)
  oneNeutralRight : ∀ g : G, g * one' = g
  invertible : ∀ g : G, ∃ g' : G, g * g' = one'

#print Group

end

namespace Group

section

variable {G : Magma} [h : Group G]

local infixl:70 " * " => id' Magma.law G
@[appUnexpander id'] def unexpandMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => h.one' -- HACK

theorem inverseComm {g h : G} (inv : g * h = one) : h * g = one :=
by match Group.invertible h with
| ⟨ k, inv' ⟩ =>
  have p₁ : h * g = h * g * one := (Group.oneNeutralRight _).symm
  have p₂ : h * g * one = h * g * h * k := by rw [Group.assoc (h * g), inv']
  have p₃ : h * g * h * k = h * k := by rw [Group.assoc h, inv, Group.oneNeutralRight]
  exact p₁.trans <| p₂.trans $ p₃.trans inv'

@[simp]
protected theorem oneNeutralRight' (g : G) : g * one = g := Group.oneNeutralRight g

@[simp]
theorem oneNeutralLeft (g : G) : one * g = g :=
by match Group.invertible g with
| ⟨ h, inv ⟩ =>
  rw [← inv, Group.assoc, inverseComm inv, Group.oneNeutralRight]

theorem inverseUnique {g h h' : G} (h₁ : g * h = one) (h₂ : g * h' = one) : h = h' :=
by
  have p₁ : g * h = g * h' := h₂.symm ▸ h₁
  have p₂ : h * g * h = h * g * h' := by simp [Group.assoc h, p₁]
  simp [inverseComm h₁, oneNeutralLeft] at p₂
  exact p₂

def inv (g : G) : G := (Group.invertible g).1

notation g "⁻¹" => inv g

@[simp]
theorem invCancelRight (g : G) : g * g⁻¹ = one := (Group.invertible g).2

@[simp]
theorem invCancelLeft (g : G) : g⁻¹ * g = one := inverseComm (invCancelRight g)

@[simp]
theorem invCancelRightTail {g₀ : G} (g : G) : g₀ * g * g⁻¹ = g₀ := by rw [assoc]; simp

@[simp]
theorem invCancelLeftTail {g₀ : G} (g : G) : g₀ * g⁻¹ * g = g₀ := by rw [assoc]; simp

@[simp]
theorem normalizeAssoc (g₁ g₂ g₃ : G) : g₁ * (g₂ * g₃) = g₁ * g₂ * g₃ := (assoc _ _ _).symm

theorem isInvOfCancelLeft {g h : G} (inv : g * h = one) : h = g⁻¹ :=
inverseUnique inv <| invCancelRight g

theorem isInvOfCancelRight {g h : G} (inv : h * g = one) : h = g⁻¹ :=
isInvOfCancelLeft <| inverseComm inv

@[simp]
theorem invInvolutive (g : G) : (g⁻¹)⁻¹ = g :=
Eq.symm <| isInvOfCancelRight $ invCancelRight g

@[simp]
theorem invMul (g g' : G) : (g * g')⁻¹ = g'⁻¹ * g⁻¹ :=
Eq.symm <| isInvOfCancelLeft <| by simp

@[simp]
theorem invOne : one⁻¹ = one := Eq.symm <| isInvOfCancelLeft <| by simp

theorem oneUnique {g : G} (h : ∃ g' : G, g' * g = g') : g = one :=
match h with
| ⟨ g', h ⟩ => by
  have p : g'⁻¹ * g' * g = g'⁻¹ * g' := by rw [Group.assoc, h]
  simp at p
  exact p

end

section

variable (G H : Magma) [Group G] [Group H]

local infixl " * " => G.law
local infixl " * " => H.law

structure Morphism where
  f : G → H
  respectMul' : ∀ g g' : G, f ((g * g') : G) = f g * f g'

end

namespace Morphism

variable {G H : Magma} [Group G] [Group H]

instance : CoeFun (Morphism G H) (fun _ => G → H) where
  coe φ := φ.f

variable (φ : Morphism G H)

local infixl " * " => id' Magma.law G
@[appUnexpander id'] def unexpandGMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x * $y)
  | _ => throw ()
local infixl " * " => id' Magma.law H
@[appUnexpander id'] def unexpandHMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law H $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => Group.one' -- HACK

@[simp]
theorem respectMul (g g' : G) : φ (g * g') = φ g * φ g' := φ.respectMul' g g'

@[simp]
theorem respectOne : φ one = one := by
  apply oneUnique
  exact ⟨ φ one, by rw [← φ.respectMul, oneNeutralRight] ⟩

@[simp]
theorem respectInv (g : G) : φ (g⁻¹) = (φ g)⁻¹ :=
isInvOfCancelLeft <| φ.respectMul g (g⁻¹) ▸ invCancelRight g ▸ φ.respectOne

end Morphism

def op (G : Magma) [Group G] : Magma := ⟨ G, λ g₁ g₂ => G.law g₂ g₁ ⟩

notation G "ᵒᵖ" => op G

instance opGroup (G : Magma) [h : Group G] : Group (Gᵒᵖ) where
  one' := h.1 -- HACK
  assoc := λ g₁ g₂ g₃ => (h.assoc g₃ g₂ g₁).symm
  oneNeutralRight := h.oneNeutralLeft
  invertible := λ g => ⟨ h.inv g, h.invCancelLeft g ⟩

@[simp]
theorem opInvolutive (G : Magma) [h : Group G] : op (op G) = G :=
match G, h with | ⟨ α, f ⟩, h => rfl

namespace opGroup

def op (G : Magma) [Group G] : Morphism G (Gᵒᵖ) where
  f := inv
  respectMul' := invMul

end opGroup

end Group
