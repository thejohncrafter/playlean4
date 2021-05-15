
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

variable (H : Set G) [sg : Subgroup G H]

local infixl:70 " * " => id' Magma.law H
@[appUnexpander id'] def normal.unexpandHMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law H $x $y) => `($x * $y)
  | _ => throw ()

class Normal where
  stable : ∀ (g : G), ∀ {h}, h ∈ H → (g * h * g⁻¹) ∈ H

end

namespace Normal

variable {H : Set G} [sg : Subgroup G H]

local infixl:70 " * " => id' Magma.law H
@[appUnexpander id'] def normal.unexpandHMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law H $x $y) => `($x * $y)
  | _ => throw ()

theorem normalIff.lemma₁ :
  (∀ (g : G), ∀ {h}, h ∈ H → g * h * g⁻¹ ∈ H) ↔
  (∀ (g : G), ∀ {h}, h ∈ H → ∃ h', h' ∈ H ∧ g * h = h' * g) :=
by
  apply Iff.intro
  focus
    intro p g h hIn
    suffices p : ∃ h', h' ∈ H ∧ g * h * g⁻¹ = h'
    from match p with
      | ⟨ h', ⟨ h'In, p ⟩ ⟩ => ⟨ h', ⟨ h'In, by simp [p.symm] ⟩ ⟩
    exact ⟨ g * h * g⁻¹, ⟨ p g hIn, rfl ⟩ ⟩
  focus
    intro p g h hIn
    match p g hIn with
    | ⟨ h', ⟨ h'In, p ⟩ ⟩ =>
      rw [show g * h * g⁻¹ = h' by simp [p]]
      simp [h'In]

theorem normalIff.lemma₂ :
  (∀ (g : G), ∀ {h}, h ∈ H → ∃ h', h' ∈ H ∧ g * h = h' * g) →
  (∀ (g : G), ∀ {h}, h ∈ H → ∃ h', h' ∈ H ∧ g * h' = h * g) :=
by
  intro h g h₀ h₀In
  match h (g⁻¹) (sg.invMem h₀In) with
  | ⟨ h', ⟨ h'In, p ⟩ ⟩ =>
    have ∀ k k' : G, k = k' → k⁻¹ = k'⁻¹ by intro _ _ h; rw [h]
    have p' := this _ _ p
    simp at p'
    exact ⟨ h'⁻¹, ⟨ sg.invMem h'In, p'.symm ⟩ ⟩

theorem normalIff.lemma₃ :
  (∀ (g : G), ∀ {h}, h ∈ H → ∃ h', h' ∈ H ∧ g * h = h' * g) →
  (∀ (g : G), ∀ {h}, h ∈ H → ∃ h', h' ∈ H ∧ g * h' = h * g) →
  ∀ (P : G → Prop), P ∈ leftClasses H → P ∈ rightClasses H :=
by
  intro h₀ h₁ p h'
  match h' with
  | ⟨ g, h' ⟩ =>
    apply Exists.intro g
    rw [h']
    simp [Action.Remarkable.onSelf]
    exact funext <| λ x => propext ⟨ (λ h'' => match h'' with
      | ⟨ k, ⟨ kIn, h'' ⟩ ⟩ => match h₀ g kIn with
        | ⟨ k', ⟨ k'In, h''' ⟩ ⟩ => ⟨ k', ⟨ k'In,
          by rw [h'']; simp [id'] at h'''; simp [id']; rw [h''']; rfl ⟩ ⟩),
      (λ h'' => match h'' with
      | ⟨ k, ⟨ kIn, h'' ⟩ ⟩ => match h₁ g kIn with
        | ⟨ k', ⟨ k'In, h''' ⟩ ⟩ => ⟨ k', ⟨ k'In,
          by rw [h'']; simp [id'] at h'''; simp [id']; rw [h''']; rfl ⟩ ⟩) ⟩

theorem normalIff.lemma₄ :
  (∀ (g : G), ∀ {h}, h ∈ H → ∃ h', h' ∈ H ∧ g * h = h' * g) →
  (∀ (g : G), ∀ {h}, h ∈ H → ∃ h', h' ∈ H ∧ g * h' = h * g) →
  ∀ (P : G → Prop), P ∈ rightClasses H → P ∈ leftClasses H :=
by
  rw [← leftClassesOnOp, ← rightClassesOnOp]
  exact λ h₁ h₂ p h => @normalIff.lemma₃ _ _ (Hᵒᵖ)
    (λ g h hIn => match h₂ g hIn with
      | ⟨ k, ⟨ kIn, h₂ ⟩ ⟩ => ⟨ k, ⟨ kIn, h₂.symm ⟩ ⟩)
    (λ g h hIn => match h₁ g hIn with
      | ⟨ k, ⟨ kIn, h₁ ⟩ ⟩ => ⟨ k, ⟨ kIn, h₁.symm ⟩ ⟩)
    p h

theorem normalIff.lemma₅ :
  (∀ (P : Set G), P ∈ rightClasses H ↔ P ∈ leftClasses H) →
  (∀ (g : G), ∀ {h}, h ∈ H → ∃ h', h' ∈ H ∧ g * h = h' * g) :=
by
  intro h g h₀ h₀In
  have p := ((leftClassOf H g).property)
  rw [← h] at p
  have p₁ := leftClassMemIff H ((leftClassOf H g).2)
    (memOfLeftClassOf H g) (g * h₀)
  have p₂ := rightClassMemIff H p
    (memOfLeftClassOf H g) (g * h₀)
  exact (p₁.trans p₂).1 ⟨ h₀, ⟨ h₀In, rfl ⟩ ⟩

end Normal

end Subgroup

namespace Morphism

variable {G H : Magma} [Group G] [Group H] (φ : Morphism G H)

local infixl:70 " * " => id' Magma.law G
local infix:70 " * " => id' Magma.law H

def kernel : Set G := λ g => φ g = one'

def kernelIsSubgroup : Subgroup G (kernel φ) := Subgroup.ofInhabitedMulInvStable
  (⟨ one', φ.respectOne ⟩)
  (λ {h} hIn h' h'In => by simp [kernel, Set.mem]; rw [hIn, h'In]; simp )

instance kernelIsNormal : Subgroup.Normal (φ.kernel) where
  stable := λ g k kIn => by
    suffices p : φ (g * (k : G) * g⁻¹) = one'
    by exact p
    have p : φ k = one' := kIn
    simp [φ.respectMul, p]

end Morphism

end Group
