
import Playlean4.Group.Basic
import Playlean4.Group.Subgroup
import Playlean4.Group.LRClasses
import Playlean4.Group.OnSet

namespace Group

namespace Subgroup

variable {G : Magma} [grp : Group G]

local infixl:70 " * " => id' Magma.law G
@[appUnexpander id'] def normal.UnexpandGMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => grp.one' -- HACK

section

variable (H : Set G) [sg : Subgroup G H]

local infixl:70 " * " => id' Magma.law H
@[appUnexpander id'] def normal.unexpandHMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law H $x $y) => `($x * $y)
  | _ => throw ()

class Normal where
  stable : ∀ (g : G), ∀ {h}, h ∈ H → (g * h * g⁻¹) ∈ H

end

end Subgroup

-- Start with the simple things : the kernel is always normal
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

namespace Subgroup

variable {G : Magma} [grp : Group G]

local infixl:70 " * " => id' Magma.law G
@[appUnexpander id'] def normal.UnexpandGMul' : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => grp.one' -- HACK

-- Now prove the converse : a normal subgroup is the kernel of some function
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

section

variable [normal : Normal H]

open Action.Remarkable.OnSet

theorem conjH (g : G) : g •• H = H :=
by
  funext h
  apply propext
  suffices (∃ h', h' ∈ H ∧ h = g * h' * g⁻¹) ↔ h ∈ H by exact this
  exact ⟨ λ p => match p with
    | ⟨ h', ⟨ h'In, p ⟩ ⟩ => p ▸ normal.stable g h'In,
    λ p => ⟨ (g⁻¹ * h * (g⁻¹⁻¹)), ⟨ normal.stable (g⁻¹) p, by simp ⟩ ⟩ ⟩

theorem moveLeft (g : G) : H •ᵣ g = g •ₗ H :=
by
  rw [show H •ᵣ g = (g •• H) •ᵣ g by rw [conjH]]
  rw [conjugationCompat, ← rightTranslationCompat, invCancelLeft, rightTranslationIdentity]

theorem neutralRight (g : G) : (g •ₗ H) ** H = g •ₗ H :=
by
  funext x
  apply propext
  apply Iff.intro
  exact λ h => match h with
  | ⟨ res, ⟨ h₁, h₁In, resEq ⟩, h₂, h₂In, h₂Eq ⟩ =>
    ⟨ h₁ * h₂, sg.mulMem h₁In h₂In, by
      rw [h₂Eq, resEq]
      suffices g * h₁ * h₂ = g * (h₁ * h₂) by exact this
      simp ⟩
  exact λ h => match h with
    | ⟨ h, hIn, xEq ⟩ =>
      ⟨ g * h, ⟨ h, hIn, rfl ⟩, one, oneMem, by
        rw [xEq]
        suffices g * h = g * h * one by exact this
        simp ⟩

/-! "pseudo morphism" because there is no notion of magma morphisms (yet !) -/
theorem pseudoMorphism (g : G) (g' : G) : (g •ₗ H) ** (g' •ₗ H) = (g * g') •ₗ H :=
by
  have p : g •ₗ (g' •ₗ H) = (g * g') •ₗ H
  from (leftActionOnSet.compat g g' H).symm
  rw [mulOnSetCompat₁, translationCompat, moveLeft, p, neutralRight]

theorem leftClassesStable {P Q : Set G}
  (PIn : P ∈ leftClasses H) (QIn : Q ∈ leftClasses H) : P ** Q ∈ leftClasses H :=
by
  rw [leftClassIff] at PIn
  rw [leftClassIff] at QIn
  rw [leftClassIff]
  match PIn, QIn with
  | ⟨ g, PIs ⟩, ⟨ g', QIs ⟩ =>
    rw [PIs, QIs]
    rw [pseudoMorphism]
    exact ⟨ g * g', rfl ⟩

def quotientLaw : leftClasses H → leftClasses H → leftClasses H :=
  λ P Q => ⟨ P ** Q, leftClassesStable P.2 Q.2 ⟩

instance quotientGroup : Group ⟨ (leftClasses H), quotientLaw ⟩ where
  one' := subgroupAsLeftClass H
  assoc := λ P₁ P₂ P₃ => by
    apply Subtype.eq
    simp [id', quotientLaw]
    match (leftClassIff _ _).2 P₁.2,
      (leftClassIff _ _).2 P₂.2,
      (leftClassIff _ _).2 P₃.2 with
    | ⟨ g₁, (P₁Is : P₁ = g₁ •ₗ H) ⟩,
      ⟨ g₂, (P₂Is : P₂ = g₂ •ₗ H) ⟩,
      ⟨ g₃, (P₃Is : P₃ = g₃ •ₗ H) ⟩ =>
      rw [P₁Is, P₂Is, P₃Is]
      simp [pseudoMorphism]
  oneNeutralRight := λ P => by
    apply Subtype.eq
    simp only [id', quotientLaw]
    exact match (leftClassIff _ _).2 P.2 with
    | ⟨ g, PIs ⟩ => PIs ▸ neutralRight _
  invertible := λ P => by
    simp only [id', quotientLaw]
    match (leftClassIff _ _).2 P.2 with
    | ⟨ g, (PIs : P = g •ₗ H)⟩ =>
      apply Exists.intro (leftClassOf H (g⁻¹))
      apply Subtype.eq
      suffices P.1 ** (g⁻¹ •ₗ H) = H by exact this
      rw [PIs]
      simp only [pseudoMorphism, invCancelRight]
      exact leftActionOnSet.identity H

def canonicalSurjection : Morphism G ⟨ (leftClasses H), quotientLaw ⟩ where
  f := λ g => ⟨ g •ₗ H, by
    rw [leftClassIff]
    exact ⟨ g, rfl ⟩ ⟩
  respectMul' := λ g g' => Subtype.eq <| (pseudoMorphism _ _).symm

end

end Normal

end Subgroup

end Group
