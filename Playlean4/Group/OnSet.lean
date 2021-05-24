
import Playlean4.Basic
import Playlean4.Group.Basic
import Playlean4.Group.Subgroup
import Playlean4.Group.Action

set_option quotPrecheck.allowSectionVars true

namespace Group.Action.Remarkable

namespace OnSet

variable {G : Type} (law : G → G → G) [grp : Group G law]

local infixl:70 " * " => id' law
@[appUnexpander id'] def unexpandGMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => grp.one' -- HACK
local notation g"⁻¹" => grp.inv g

def leftTranslationOnSet : G → Set G → Set G := (liftToSet (onSelf law))
def rightTranslationOnSet : G → Set G → Set G := (@liftToSet G _ (onSelf (lawᵒᵖ)))
def conjugationOnSet : G → Set G → Set G := (liftToSet (conjugation law))

local infix:70 " •ₗ " => leftTranslationOnSet law
local notation:70 lhs:70 " •ᵣ " rhs:70 => rightTranslationOnSet law rhs lhs
local infix:70 " ••  " => conjugationOnSet law

instance leftActionOnSet : Action G law (leftTranslationOnSet law) := sorry

theorem rightTranslationIdentity (P : Set G) : P •ᵣ one = P :=
((@actionOnSet G (lawᵒᵖ) _ _ (onSelf (lawᵒᵖ)) _).identity P)

theorem rightTranslationCompat (g g' : G) (P : Set G) : (P •ᵣ (g * g')) = (P •ᵣ g) •ᵣ g' :=
(@actionOnSet G (lawᵒᵖ) _ _ (onSelf (lawᵒᵖ)) _).compat g' g P

theorem translationCompat (g g' : G) (P : Set G) : (g •ₗ P) •ᵣ g' = g •ₗ (P •ᵣ g') :=
by
  simp only [leftTranslationOnSet, rightTranslationOnSet, liftToSet, Set.imgComp]
  apply Set.imgCongrFun
  funext x
  suffices g * x * g' = g * (x * g') by exact this
  simp

theorem conjugationCompat (g : G) (P : Set G) : g •• P = (g •ₗ P) •ᵣ g⁻¹ :=
by
  simp only [leftTranslationOnSet, rightTranslationOnSet, conjugationOnSet, liftToSet, Set.imgComp]
  apply Set.imgCongrFun
  rfl

def mulOnSet : Set G → Set G → Set G := λ P Q =>
  λ h => ∃ g, g ∈ P ∧ ∃ g', g' ∈ Q ∧ h = g * g'

local infixl:70 " ** " => mulOnSet law

def mulOnSetCompat₁ (P Q : Set G) (g : G) : P ** (g •ₗ Q) = (P •ᵣ g) ** Q :=
by
  funext x
  apply propext
  have p₁ : (P ** (g •ₗ Q)) x ↔ ∃ p, p ∈ P ∧ ∃ q, q ∈ Q ∧ x = p * (g * q)
  by
    apply Iff.intro
    exact λ h => match h with
      | ⟨ p, pIn, res, ⟨ q, qIn, resEq ⟩, xEq ⟩ =>
        ⟨ p, pIn, q, qIn, xEq ▸ resEq ▸ rfl ⟩
    exact λ h => match h with
      | ⟨ p, pIn, q, qIn, h ⟩ =>
        ⟨ p, pIn, g * q, ⟨ q, qIn, rfl ⟩, h ⟩
  have p₂ : (∃ p, p ∈ P ∧ ∃ q, q ∈ Q ∧ x = p * g * q) ↔ ((P •ᵣ g) ** Q) x
  by
    apply Iff.intro
    exact λ h => match h with
      | ⟨ p, pIn, q, qIn, h ⟩ =>
        ⟨ p * g, ⟨ p, pIn, rfl ⟩, q, qIn, h ⟩
    exact λ h => match h with
      | ⟨ res, ⟨ p, pIn, resEq ⟩, q, qIn, xEq ⟩ =>
        ⟨ p, pIn, q, qIn, xEq ▸ resEq ▸ rfl ⟩
  have p₃ : (∃ p, p ∈ P ∧ ∃ q, q ∈ Q ∧ x = p * (g * q)) ↔
    ∃ p, p ∈ P ∧ ∃ q, q ∈ Q ∧ x = p * g * q
  by simp
  exact p₁.trans <| p₃.trans p₂

end OnSet

end Group.Action.Remarkable
