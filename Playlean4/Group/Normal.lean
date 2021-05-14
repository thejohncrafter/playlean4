
import Playlean4.Group.Basic
import Playlean4.Group.Subgroup
import Playlean4.Group.LRClasses

namespace Group

namespace Subgroup

variable {G : Magma} [h : Group G]

local infixl:70 " * " => id' Magma.law G
@[appUnexpander id'] def normal.UnexpandGMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => h.one' -- HACK

section

variable (H : Subgroup G)

local infixl:70 " * " => id' Magma.law H
@[appUnexpander id'] def normal.unexpandHMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law H $x $y) => `($x * $y)
  | _ => throw ()

class Normal where
  stable : ∀ (g : G) (h : H), H.p (g * h * g⁻¹)

end

namespace Normal

variable {H : Subgroup G}

local infixl:70 " * " => id' Magma.law H
@[appUnexpander id'] def normal.unexpandHMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law H $x $y) => `($x * $y)
  | _ => throw ()

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
  exact λ h₁ h₂ p h => @normalIff.lemma₃ _ _ (op H)
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

end Normal

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
