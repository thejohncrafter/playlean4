
import Playlean4.Group.Basic
import Playlean4.Group.Subgroup

namespace Group

namespace Subgroup

variable {G : Magma} [h : Group G]

local infixl:70 " * " => id' Magma.law G
@[appUnexpander id'] def unexpandGMul' : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => h.one' -- HACK

section

variable (H : Subgroup G)

local infixl:70 " * " => id' Magma.law H
@[appUnexpander id'] def unexpandHMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law H $x $y) => `($x * $y)
  | _ => throw ()

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

end

variable {H : Subgroup G}

local infixl:70 " * " => id' Magma.law H
@[appUnexpander id'] def unexpandHMul' : Lean.PrettyPrinter.Unexpander
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

theorem rightClassIsOpLeftClass (g : G) : rightClassOf H g = leftClassOf (op H) g :=
Subtype.eq <| by
  funext x
  apply propext <| Iff.intro
    (λ h => ⟨ h.1, h.2 ▸ rfl ⟩)
    (λ h => ⟨ h.1, h.2 ▸ rfl ⟩)

theorem rightClassOnOp : isRightClass H = isLeftClass (op H) := rfl
theorem leftClassOnOp : isLeftClass H = isRightClass (op H) := rfl
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
@leftClassMemIff _ _ (op H) c g g'

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
@leftClassEqIff.lemma₁ _ _ (op H) c₁ c₂

theorem rightClassEqIff.lemma₂ (c₁ c₂ : rightClass H) :
  (∃ (g₁ : (c₁ : Type)) (g₂ : (c₂ : Type)), ∃ h : H, (g₁ : G) = (h : G) * (g₂ : G)) →
  ∀ (g₁ : (c₁ : Type)) (g₂ : (c₂ : Type)), ∃ h : H, (g₁ : G) = (h : G) * (g₂ : G) :=
@leftClassEqIff.lemma₂ _ _ (op H) c₁ c₂

theorem rightClassEqIff.lemma₃ (c₁ c₂ : rightClass H) :
  (∀ (g₁ : (c₁ : Type)) (g₂ : (c₂ : Type)),
    ∃ h : H, (g₁ : G) = (h : G) * (g₂ : G)) → c₁ = c₂ :=
@leftClassEqIff.lemma₃ _ _ (op H) c₁ c₂

-- TODO : Same thing here

end Subgroup

end Group
