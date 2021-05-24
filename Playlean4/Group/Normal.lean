
import Playlean4.Group.Basic
import Playlean4.Group.Subgroup
import Playlean4.Group.LRClasses
import Playlean4.Group.OnSet

namespace Group

namespace Subgroup

variable {G : Type} (law : G → G → G) [grp : Group G law]

local infixl:70 " * " => id' law
@[appUnexpander id'] def normal.UnexpandGMul : Lean.PrettyPrinter.Unexpander
  | `(id' law $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => grp.one' -- HACK
local notation g"⁻¹" => grp.inv g

section

variable (H : Set G) [sg : Subgroup G law H]

local infixl:70 " * " => id' (subgroupLaw law H)
@[appUnexpander id'] def normal.unexpandHMul : Lean.PrettyPrinter.Unexpander
  | `(id' (subgroupLaw law H) $x $y) => `($x * $y)
  | _ => throw ()

class Normal where
  stable : ∀ (g : G), ∀ {h}, h ∈ H → (g * h * g⁻¹) ∈ H

end

end Subgroup

-- Start with the simple things : the kernel is always normal
namespace Morphism

variable {G : Type} {lawG : G → G → G} [grpG : Group G lawG]
variable {H : Type} {lawH : H → H → H} [grpH : Group H lawH]
variable (φ : Morphism G lawG H lawH)

local infixl:70 " * " => id' lawG
local notation g"⁻¹" => grpG.inv g
local infix:70 " * " => id' lawH
local notation g"⁻¹" => grpH.inv g

def kernel : Set G := λ g => φ g = grpH.one'

def kernelIsSubgroup : Subgroup G lawG (kernel φ) := Subgroup.ofInhabitedMulInvStable lawG
  (⟨ grpG.one', φ.respectOne ⟩)
  (λ {h} hIn h' h'In => by simp [kernel, Set.mem]; rw [hIn, h'In]; simp )

instance kernelIsNormal : Subgroup.Normal lawG (φ.kernel) where
  stable := λ g k kIn => by
    suffices p : φ (g * (k : G) * g⁻¹) = grpH.one'
    by exact p
    have p : φ k = grpH.one' := kIn
    simp [φ.respectMul, p]

end Morphism

namespace Subgroup

variable {G : Type} {law : G → G → G} [grp : Group G law]

local infixl:70 " * " => id' law
@[appUnexpander id'] def normal.UnexpandGMul' : Lean.PrettyPrinter.Unexpander
  | `(id' law $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => grp.one' -- HACK
local notation g"⁻¹" => grp.inv g

-- Now prove the converse : a normal subgroup is the kernel of some function
namespace Normal

variable (H : Set G) [sg : Subgroup G law H]

local infixl:70 " * " => id' (subgroupLaw law H)
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
  ∀ (P : G → Prop), P ∈ leftClasses law H → P ∈ rightClasses law H :=
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
  ∀ (P : G → Prop), P ∈ rightClasses law H → P ∈ leftClasses law H :=
by
  rw [← leftClassesOnOp, ← rightClassesOnOp]
  exact λ h₁ h₂ p h => @normalIff.lemma₃ _ (lawᵒᵖ) _ H
    (λ g h hIn => match h₂ g hIn with
      | ⟨ k, ⟨ kIn, h₂ ⟩ ⟩ => ⟨ k, ⟨ kIn, h₂.symm ⟩ ⟩)
    (λ g h hIn => match h₁ g hIn with
      | ⟨ k, ⟨ kIn, h₁ ⟩ ⟩ => ⟨ k, ⟨ kIn, h₁.symm ⟩ ⟩)
    p h

theorem normalIff.lemma₅ :
  (∀ (P : Set G), P ∈ rightClasses law H ↔ P ∈ leftClasses law H) →
  (∀ (g : G), ∀ {h}, h ∈ H → ∃ h', h' ∈ H ∧ g * h = h' * g) :=
by
  intro h g h₀ h₀In
  have p := ((leftClassOf law H g).property)
  rw [← h] at p
  have p₁ := leftClassMemIff law H ((leftClassOf law H g).2)
    (memOfLeftClassOf law H g) (g * h₀)
  have p₂ := rightClassMemIff law H p
    (memOfLeftClassOf law H g) (g * h₀)
  exact (p₁.trans p₂).1 ⟨ h₀, ⟨ h₀In, rfl ⟩ ⟩

section

variable [normal : Normal law H]

open Action.Remarkable.OnSet

local infix:70 " •ₗ " => leftTranslationOnSet law
local notation:70 lhs:70 " •ᵣ " rhs:70 => rightTranslationOnSet law rhs lhs
local infix:70 " ••  " => conjugationOnSet law
local infixl:70 " ** " => mulOnSet law

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
  from ((leftActionOnSet law).compat g g' H).symm
  rw [mulOnSetCompat₁, translationCompat, moveLeft, p, neutralRight]

theorem leftClassesStable {P Q : Set G}
  (PIn : P ∈ leftClasses law H) (QIn : Q ∈ leftClasses law H) : P ** Q ∈ leftClasses law H :=
by
  rw [leftClassIff] at PIn
  rw [leftClassIff] at QIn
  rw [leftClassIff]
  match PIn, QIn with
  | ⟨ g, PIs ⟩, ⟨ g', QIs ⟩ =>
    rw [PIs, QIs]
    rw [pseudoMorphism]
    exact ⟨ g * g', rfl ⟩

def quotientLaw : leftClasses law H → leftClasses law H → leftClasses law H :=
  λ P Q => ⟨ P ** Q, leftClassesStable H P.2 Q.2 ⟩

instance quotientGroup : Group (leftClasses law H) (quotientLaw H) where
  one' := subgroupAsLeftClass law H
  assoc := λ P₁ P₂ P₃ => by
    apply Subtype.eq
    simp [id', quotientLaw]
    match (leftClassIff law _ _).2 P₁.2,
      (leftClassIff law _ _).2 P₂.2,
      (leftClassIff law _ _).2 P₃.2 with
    | ⟨ g₁, (P₁Is : P₁ = g₁ •ₗ H) ⟩,
      ⟨ g₂, (P₂Is : P₂ = g₂ •ₗ H) ⟩,
      ⟨ g₃, (P₃Is : P₃ = g₃ •ₗ H) ⟩ =>
      rw [P₁Is, P₂Is, P₃Is]
      simp [pseudoMorphism]
  oneNeutralRight := λ P => by
    apply Subtype.eq
    simp only [id', quotientLaw]
    exact match (leftClassIff law _ _).2 P.2 with
    | ⟨ g, PIs ⟩ => PIs ▸ neutralRight _ _
  invertible := λ P => by
    simp only [id', quotientLaw]
    match (leftClassIff law _ _).2 P.2 with
    | ⟨ g, (PIs : P = g •ₗ H)⟩ =>
      apply Exists.intro (leftClassOf law H (g⁻¹))
      apply Subtype.eq
      suffices P.1 ** (g⁻¹ •ₗ H) = H by exact this
      rw [PIs]
      simp only [pseudoMorphism, invCancelRight]
      exact (leftActionOnSet law).identity H

def canonicalSurjection : Morphism G law (leftClasses law H) (quotientLaw H) where
  f := λ g => ⟨ g •ₗ H, by
    rw [leftClassIff]
    exact ⟨ g, rfl ⟩ ⟩
  respectMul' := λ g g' => Subtype.eq <| (pseudoMorphism H _ _).symm

end

end Normal

end Subgroup

end Group
