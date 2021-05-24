
import Playlean4.Basic

set_option quotPrecheck false

section

variable (G : Type) (law : G → G → G)

local infixl:70 " * " => id' law
@[appUnexpander id'] def unexpandMul : Lean.PrettyPrinter.Unexpander
  | `(id' law $x $y) => `($x * $y)
  | _ => throw ()

class Group where
  one' : G -- Name hack
  assoc : ∀ g₁ g₂ g₃ : G, (g₁ * g₂) * g₃ = g₁ * (g₂ * g₃)
  oneNeutralRight : ∀ g : G, g * one' = g
  invertible : ∀ g : G, ∃ g' : G, g * g' = one'

end

namespace Group

section

variable {G : Type} {law : G → G → G} [grp : Group G law]

local infixl:70 " * " => id' law
@[appUnexpander id'] def unexpandMul : Lean.PrettyPrinter.Unexpander
  | `(id' law $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => grp.one' -- HACK

theorem inverseComm {g h : G} (inv : g * h = one) : h * g = one :=
by match grp.invertible h with
| ⟨ k, inv' ⟩ =>
  have p₁ : h * g = h * g * one := (Group.oneNeutralRight _).symm
  have p₂ : h * g * one = h * g * h * k := by rw [Group.assoc (h * g), inv']
  have p₃ : h * g * h * k = h * k := by rw [Group.assoc h, inv, Group.oneNeutralRight]
  exact p₁.trans <| p₂.trans $ p₃.trans inv'

@[simp]
protected theorem oneNeutralRight' (g : G) : g * one = g := Group.oneNeutralRight g

@[simp]
theorem oneNeutralLeft (g : G) : one * g = g :=
by match grp.invertible g with
| ⟨ h, inv ⟩ =>
  rw [← inv, Group.assoc, inverseComm inv, Group.oneNeutralRight]

theorem inverseUnique {g h h' : G} (h₁ : g * h = one) (h₂ : g * h' = one) : h = h' :=
by
  have p₁ : g * h = g * h' := h₂.symm ▸ h₁
  have p₂ : h * g * h = h * g * h' := by simp [grp.assoc h, p₁]
  simp [inverseComm h₁, oneNeutralLeft] at p₂
  exact p₂

def inv (g : G) : G := (grp.invertible g).1

local notation g "⁻¹" => grp.inv g

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

variable (G : Type) (lawG : G → G → G) [grpG : Group G lawG]
variable (H : Type) (lawH : H → H → H) [grpH : Group H lawH]

local infixl " * " => lawG
local infixl " * " => lawH

structure Morphism where
  f : G → H
  respectMul' : ∀ g g' : G, f ((g * g') : G) = f g * f g'

end

namespace Morphism

variable {G : Type} {lawG : G → G → G} [grpG : Group G lawG]
variable {H : Type} {lawH : H → H → H} [grpH : Group H lawH]

instance : CoeFun (Morphism G lawG H lawH) (fun _ => G → H) where
  coe φ := φ.f

variable (φ : Morphism G lawG H lawH)

local infixl " * " => id' lawG
@[appUnexpander id'] def unexpandGMul : Lean.PrettyPrinter.Unexpander
  | `(id' lawG $x $y) => `($x * $y)
  | _ => throw ()
local infixl " * " => id' lawH
@[appUnexpander id'] def unexpandHMul : Lean.PrettyPrinter.Unexpander
  | `(id' lawH $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => Group.one' -- HACK

@[simp]
theorem respectMul (g g' : G) : φ (g * g') = φ g * φ g' := φ.respectMul' g g'

@[simp]
theorem respectOne : φ (one lawG) = (one lawH) := by
  apply oneUnique
  exact ⟨ φ (one lawG), by rw [← φ.respectMul, oneNeutralRight] ⟩

@[simp]
theorem respectInv (g : G) : φ (grpG.inv g) = grpH.inv (φ g) :=
isInvOfCancelLeft <| φ.respectMul g (inv g) ▸ invCancelRight g ▸ φ.respectOne

end Morphism

def op {G : Type} (law : G → G → G) [grp : Group G law] : G → G → G := λ g₁ g₂ => law g₂ g₁

notation law "ᵒᵖ" => op law

instance opGroup (G : Type) (law : G → G → G) [h : Group G law] : Group G (lawᵒᵖ) where
  one' := h.1 -- HACK
  assoc := λ g₁ g₂ g₃ => (h.assoc g₃ g₂ g₁).symm
  oneNeutralRight := h.oneNeutralLeft
  invertible := λ g => ⟨ h.inv g, h.invCancelLeft g ⟩

@[simp]
theorem opInvolutive (G : Type) (law : G → G → G) [grp : Group G law] : op (op law) = law := rfl

namespace opGroup

def op (G : Type) (law : G → G → G) [grp : Group G law] : Morphism G law G (lawᵒᵖ) where
  f := inv
  respectMul' := invMul

end opGroup

end Group
