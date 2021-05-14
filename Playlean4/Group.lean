
set_option quotPrecheck false

universes u
def id' {α : Sort u} (a : α) : α := a

section

def Set (X : Type) := X → Prop

namespace Set

def mem {X : Type} (x : X) (s : Set X) := s x

infix:50 " ∈ " => mem

theorem ext {X : Type} (s₁ s₂ : Set X) (h : ∀ x : X, x ∈ s₁ ↔ x ∈ s₂) : s₁ = s₂ :=
by
  funext x
  exact propext <| h x

end Set

end

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

section

variable (G : Magma) [h : Group G]

local infixl:70 " * " => G.law
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

structure Subgroup where
  p : G → Prop
  oneMem : p one
  mulMem : ∀ g g' : Subtype p, p ((g : G) * g')
  invMem : ∀ g : Subtype p, p ((g : G)⁻¹)

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

namespace Subgroup

def coeMagma (H : Subgroup G) : Magma :=
  ⟨ Subtype H.p, λ g g' => ⟨ (g : G) * (g' : G), H.mulMem g g' ⟩ ⟩

instance SubgroupCoeMagma : CoeHead (Subgroup G) Magma where
  coe := coeMagma

instance SubgroupCoeCarrier : CoeSort (Subgroup G) Type where
  coe H := ((H : Magma) : Type)

instance GroupOfSubgroup (H : Subgroup G) : Group H where
  one' := ⟨ one, H.oneMem ⟩
  assoc := λ g g' g'' => Subtype.eq <| h.assoc g.val g'.val g''.val
  oneNeutralRight := λ g => Subtype.eq <| h.oneNeutralRight g.val
  invertible := λ g => ⟨ ⟨ g.val⁻¹, H.invMem g ⟩, Subtype.eq <| invCancelRight (g.val : G) ⟩

section -- "variable" doesn't work here for some reason

theorem lemma₁ {p : G → Prop}
  (inhabited : ∃ g : G, p g)
  (mulInvStable : ∀ {g g' : G}, p g → p g' → p (g * g'⁻¹)) : p one :=
match inhabited with
  | ⟨ g, h ⟩ => invCancelRight g ▸ mulInvStable h h

theorem lemma₂ {p : G → Prop}
  (inhabited : ∃ g : G, p g)
  (mulInvStable : ∀ {g g' : G}, p g → p g' → p (g * g'⁻¹)) :
    ∀ g : Subtype p, p (g⁻¹) := λ g =>
oneNeutralLeft ((g : G)⁻¹) ▸ mulInvStable (lemma₁ inhabited mulInvStable) g.2

theorem lemma₃ {p : G → Prop}
  (inhabited : ∃ g : G, p g)
  (mulInvStable : ∀ {g g' : G}, p g → p g' → p (g * g'⁻¹)) :
    ∀ g g' : Subtype p, p ((g : G) * (g' : G)) := λ g g' =>
invInvolutive g'.1 ▸ mulInvStable g.2 (lemma₂ inhabited mulInvStable g')

end

def ofInhabitedMulInvStable (p : G → Prop)
  (inhabited : ∃ g : G, p g)
  (mulInvStable : ∀ {g g' : G}, p g → p g' → p (g * g'⁻¹)) : Subgroup G where
  p := p
  oneMem := lemma₁ inhabited mulInvStable
  mulMem := lemma₃ inhabited mulInvStable
  invMem := lemma₂ inhabited mulInvStable

section

variable (H : Subgroup G)

def embedding : Morphism H G where
  f g := g.val
  respectMul' := λ g g' : Subtype H.p => by rfl

instance SubgroupCoe : CoeHead ((H : Magma) : Type) (G : Type) where
  coe := embedding H

def op : Subgroup (Gᵒᵖ) where
  p := H.p
  oneMem := H.oneMem
  mulMem := λ g g' => H.mulMem g' g
  invMem := H.invMem

notation H "ᵒᵖ" => op H

def isLeftClass (p : G → Prop) := ∃ g, p = λ g' : G => ∃ h : H, g' = (g : G) * (h : G)
def isRightClass (p : G → Prop) := ∃ g, p = λ g' : G => ∃ h : H, g' = (h : G) * (g : G)
def leftClass := Subtype (λ p : G → Prop => isLeftClass H p)
def rightClass := Subtype (λ p : G → Prop => isRightClass H p)

instance leftClassCoe (c : leftClass H) : CoeDep (leftClass H) c Type where
  coe := Subtype c.val

instance rightClassCoe (c : rightClass H) : CoeDep (rightClass H) c Type where
  coe := Subtype c.val

def leftClassOf (g : G) : leftClass H where
  val := λ g' => ∃ h : (H : Type), g' = (g : G) * (h : G)
  property := ⟨ g, rfl ⟩

def memOfleftClassOf (g : G) : (leftClassOf H g).val g :=
⟨ ⟨ one, H.oneMem ⟩, by simp [embedding] ⟩

def rightClassOf (g : G) : rightClass H where
  val := λ g' => ∃ h : (H : Type), g' = (h : G) * (g : G)
  property := ⟨ g, rfl ⟩

def memOfRightClassOf (g : G) : (rightClassOf H g).val g :=
⟨ ⟨ one, H.oneMem ⟩, by simp [embedding] ⟩

class Normal where
  stable : ∀ (g : G) (h : H), H.p (g * h * g⁻¹)

end

variable {H : Subgroup G}

local infixl:70 " * " => id' Magma.law H
@[appUnexpander id'] def unexpandHMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law H $x $y) => `($x * $y)
  | _ => throw ()

instance (c : leftClass H) : Inhabited (c : Type) where
  default :=
    ⟨ (c.property.1 : G) * ((⟨ one, H.oneMem ⟩ : H) : G),
      c.property.2 ▸ Exists.intro ⟨ one, H.oneMem ⟩ (by rfl) ⟩

theorem leftClassIsGenerated (c : leftClass H) : ∃ g : G, c = leftClassOf H g :=
⟨ c.property.1, Subtype.eq <| c.property.2 ▸ rfl ⟩

theorem rightClassIsGenerated (c : rightClass H) : ∃ g : G, c = rightClassOf H g :=
⟨ c.property.1, Subtype.eq <| c.property.2 ▸ rfl ⟩

theorem rightClassIsOpLeftClass (g : G) : rightClassOf H g = leftClassOf (H.op) g :=
Subtype.eq <| by
  funext x
  apply propext <| Iff.intro
    (λ h => ⟨ h.1, h.2 ▸ rfl ⟩)
    (λ h => ⟨ h.1, h.2 ▸ rfl ⟩)

theorem rightClassOnOp : isRightClass H = isLeftClass H.op := rfl
theorem leftClassOnOp : isLeftClass H = isRightClass H.op := rfl
-- We also get : theorem rightClassOnOp' : rightClass H = leftClass H.op := rfl

theorem leftClassMemIff (c : leftClass H) (g : (c : Type)) (g' : G) :
  c.val g' ↔ ∃ h : H, g' = (g : G) * (h : G) :=
have prop₀ : ∀ g : Subtype c.val, ∃ h : H, g = c.property.1 * (h : G)
from λ ⟨ g, h ⟩ => by rw [c.property.2] at h; exact h
Iff.intro
  (λ g'h => by
    rw [c.property.2] at g'h
    match prop₀ g, g'h with
    | ⟨ h₀, h₀h ⟩, ⟨ h₁, h₁h ⟩ =>
      apply Exists.intro ((h₀⁻¹ * h₁) : H)
      simp [h₀h, h₁h])
  (λ h => match prop₀ g, h with
    | ⟨ h₀, h₀h ⟩, ⟨ h₁, h₁h ⟩ =>
      c.property.2 ▸ (Exists.intro (h₀ * h₁) <| (Group.assoc _ _ _) ▸ h₀h ▸ h₁h ▸ rfl))

theorem rightClassMemIff (c : rightClass H) (g : (c : Type)) (g' : G) :
  c.val g' ↔ ∃ h : H, g' = (h : G) * (g : G) :=
@leftClassMemIff _ _ H.op c g g'

theorem translator {c : leftClass H} (g g' : Subtype c.val) :
  ∃ h : H, g' = (g : G) * (h : G) :=
(leftClassMemIff c g g'.val).1 g'.2

theorem leftClassEqIff.lemma₁ (c₁ c₂ : leftClass H) : c₁ = c₂ →
  ∃ (g₁ : (c₁ : Type)) (g₂ : (c₂ : Type)), ∃ h : H, (g₁ : G) = (g₂ : G) * (h : G) :=
λ h => h ▸ ⟨ arbitrary, ⟨ arbitrary, ⟨ ⟨ one, H.oneMem ⟩, by simp [embedding] ⟩ ⟩ ⟩

theorem leftClassEqIff.lemma₂ (c₁ c₂ : leftClass H) :
  (∃ (g₁ : (c₁ : Type)) (g₂ : (c₂ : Type)), ∃ h : H, (g₁ : G) = (g₂ : G) * (h : G)) →
  ∀ (g₁ : (c₁ : Type)) (g₂ : (c₂ : Type)), ∃ h : H, (g₁ : G) = (g₂ : G) * (h : G) :=
λ p g₁ g₂ => match p with
| ⟨ g₃, ⟨ g₄, ⟨ h, p ⟩ ⟩ ⟩ =>
  match translator g₃ g₁, translator g₂ g₄ with
  | ⟨ h₁, p₁ ⟩, ⟨ h₂, p₂ ⟩ =>
    ⟨ (h₂ * h * h₁), by simp [p₂, p, p₁] ⟩

theorem leftClassEqIff.lemma₃' (c₁ c₂ : leftClass H)
  (x : G)
  (h : ∀ (g₁ : (c₁ : Type)) (g₂ : (c₂ : Type)),
    ∃ h : H, (g₁ : G) = (g₂ : G) * (h : G)) :
  (∃ h : H, x = c₁.property.1 * (h : G)) → (∃ h : H, x = c₂.property.1 * (h : G)) :=
by
  have prop₀ : ∀ c : leftClass H, c.val (c.property.1)
  from λ c => c.property.2 ▸ ⟨ one', by simp ⟩
  intro h'
  match h ⟨ c₁.property.1, prop₀ c₁ ⟩ ⟨ c₂.property.1, prop₀ c₂ ⟩, h' with
  | ⟨ h₀, h ⟩, ⟨ h₁, h' ⟩ =>
    simp at h
    apply Exists.intro ((h₀ * h₁) : H)
    simp [h, h']

theorem leftClassEqIff.lemma₃ (c₁ c₂ : leftClass H) :
  (∀ (g₁ : (c₁ : Type)) (g₂ : (c₂ : Type)),
    ∃ h : H, (g₁ : G) = (g₂ : G) * (h : G)) → c₁ = c₂ :=
by
  intro h
  have h' : ∀ (g₁ : (c₂ : Type)) (g₂ : (c₁ : Type)),
    ∃ h : H, (g₁ : G) = (g₂ : G) * (h : G)
  from λ g₁ g₂ => match h g₂ g₁ with
    | ⟨ h₀, h ⟩ => ⟨ h₀⁻¹, by simp [h] ⟩
  apply Subtype.eq
  rw [c₁.property.2, c₂.property.2]
  funext x
  exact propext ⟨ λ h₁ => leftClassEqIff.lemma₃' c₁ c₂ x h h₁,
    λ h₁ => leftClassEqIff.lemma₃' c₂ c₁ x h' h₁ ⟩

-- TODO : Generate a theorem that states that all these properties are equivalent

theorem rightClassEqIff.lemma₁ (c₁ c₂ : rightClass H) : c₁ = c₂ →
  ∃ (g₁ : (c₁ : Type)) (g₂ : (c₂ : Type)), ∃ h : H, (g₁ : G) = (h : G) * (g₂ : G) :=
@leftClassEqIff.lemma₁ _ _ (H.op) c₁ c₂

theorem rightClassEqIff.lemma₂ (c₁ c₂ : rightClass H) :
  (∃ (g₁ : (c₁ : Type)) (g₂ : (c₂ : Type)), ∃ h : H, (g₁ : G) = (h : G) * (g₂ : G)) →
  ∀ (g₁ : (c₁ : Type)) (g₂ : (c₂ : Type)), ∃ h : H, (g₁ : G) = (h : G) * (g₂ : G) :=
@leftClassEqIff.lemma₂ _ _ (H.op) c₁ c₂

theorem rightClassEqIff.lemma₃ (c₁ c₂ : rightClass H) :
  (∀ (g₁ : (c₁ : Type)) (g₂ : (c₂ : Type)),
    ∃ h : H, (g₁ : G) = (h : G) * (g₂ : G)) → c₁ = c₂ :=
@leftClassEqIff.lemma₃ _ _ (H.op) c₁ c₂

-- TODO : Same thing here

theorem normalIff.lemma₁ :
  (∀ (g : G) (h : H), H.p (g * h * g⁻¹)) ↔
  (∀ (g : G) (h : H), ∃ h' : H, g * h = h' * g) :=
by
  apply Iff.intro
  focus
    intro p g h
    suffices p : ∃ h' : H, g * h * g⁻¹ = h'
    from match p with
      | ⟨ h', p ⟩ => ⟨ h', by simp [p.symm] ⟩
    exact ⟨ ⟨ g * h * g⁻¹, p g h ⟩, rfl ⟩
  focus
    intro p g h
    match p g h with
    | ⟨ h', p ⟩ =>
      rw [show g * h * g⁻¹ = h' by simp [p]]
      simp [embedding, h'.2]

theorem normalIff.lemma₂ :
  (∀ (g : G) (h : H), ∃ h' : H, g * h = h' * g) →
  (∀ (g : G) (h : H), ∃ h' : H, g * h' = h * g) :=
by
  intro h g h₀
  match h (g⁻¹) (h₀⁻¹) with
  | ⟨ h', p ⟩ =>
    have ∀ k k' : G, k = k' → k⁻¹ = k'⁻¹ by intro _ _ h; rw [h]
    have p' := this _ _ p
    simp at p'
    exact ⟨ h'⁻¹, p'.symm ⟩

theorem normalIff.lemma₃ :
  (∀ (g : G) (h : H), ∃ h' : H, g * h = h' * g) →
  (∀ (g : G) (h : H), ∃ h' : H, g * h' = h * g) →
  ∀ (p : G → Prop), isLeftClass H p → isRightClass H p :=
by
  intro h₀ h₁ p h'
  match h' with
  | ⟨ g, h' ⟩ =>
    apply Exists.intro g
    rw [h']
    exact funext <| λ x => propext ⟨ (λ h'' => match h'' with
      | ⟨ k, h'' ⟩ => match h₀ g k with
        | ⟨ k', h''' ⟩ => ⟨ k', h''' ▸ h'' ⟩),
      (λ h'' => match h'' with
      | ⟨ k, h'' ⟩ => match h₁ g k with
        | ⟨ k', h''' ⟩ => ⟨ k', h''' ▸ h'' ⟩) ⟩

theorem normalIff.lemma₄ :
  (∀ (g : G) (h : H), ∃ h' : H, g * h = h' * g) →
  (∀ (g : G) (h : H), ∃ h' : H, g * h' = h * g) →
  ∀ (p : G → Prop), isRightClass H p → isLeftClass H p :=
by
  rw [leftClassOnOp, rightClassOnOp]
  exact λ h₁ h₂ p h => @normalIff.lemma₃ _ _ H.op
    (λ g h => match h₂ g h with | ⟨ k, h₂ ⟩ => ⟨ k, h₂.symm ⟩)
    (λ g h => match h₁ g h with | ⟨ k, h₁ ⟩ => ⟨ k, h₁.symm ⟩)
    p h

theorem normalIff.lemma₅ :
  (∀ (p : G → Prop), isRightClass H p ↔ isLeftClass H p) →
  (∀ (g : G) (h : H), ∃ h' : H, g * h = h' * g) :=
by
  intro h g h₀
  have p := ((leftClassOf H g).property)
  rw [← h] at p
  have p₁ := leftClassMemIff _ ⟨ g, memOfleftClassOf H g ⟩ (g * h₀)
  have p₂ := rightClassMemIff ⟨ (leftClassOf H g).val, p ⟩ ⟨ g, memOfleftClassOf H g ⟩ (g * h₀)
  exact (p₁.trans p₂).1 ⟨ h₀, rfl ⟩

end Subgroup

namespace Morphism

variable {G H : Magma} [Group G] [Group H] (φ : Morphism G H)

local infixl:70 " * " => id' Magma.law G
local infix:70 " * " => id' Magma.law H

def kernel : Subgroup G := Subgroup.ofInhabitedMulInvStable
  (λ g => φ g = one')
  (⟨ one', φ.respectOne ⟩)
  (λ h h' => by simp at h; simp at h'; simp [h, h'] )

instance kernelIsNormal : Subgroup.Normal (φ.kernel) where
  stable := λ g k => by
    suffices p : φ (g * (k : G) * g⁻¹) = one'
    by exact p
    have p : φ k = one' := k.2
    simp [φ.respectMul, p]

end Morphism

end Group

namespace Group

variable (G : Magma) [Group G]

local infixl:65 " + " => id' Magma.law G
@[appUnexpander id'] def unexpandAdd : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x + $y)
  | _ => throw ()

class Abelian extends Group G where
  commute : ∀ g g' : G, g + g' = g' + g

variable [Abelian G]

theorem aa : ∀ g₁ g₂ g₂ : G, g₁ + g₂ + (g₃ : G) = g₃ + g₂ + g₁ :=
by
  --rw [assoc]
  admit

end Group

