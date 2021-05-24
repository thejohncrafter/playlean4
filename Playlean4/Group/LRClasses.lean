
import Playlean4.Group.Basic
import Playlean4.Group.Subgroup
import Playlean4.Group.Action
import Playlean4.Group.OnSet

set_option quotPrecheck.allowSectionVars true

namespace Group

namespace Subgroup

variable {G : Type} (law : G → G → G) [grp : Group G law]

local infixl:70 " * " => id' law
@[appUnexpander id'] def unexpandGMul' : Lean.PrettyPrinter.Unexpander
  | `(id' law $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => grp.one' -- HACK
local notation g"⁻¹" => grp.inv g

section

variable (H : Set G) [sg : Subgroup G law H]

local infixl:70 " * " => id' (subgroupLaw law H)
@[appUnexpander id'] def unexpandHMul : Lean.PrettyPrinter.Unexpander
  | `(id' (subgroupLaw law H) $x $y) => `($x * $y)
  | _ => throw ()

local infix:70 " •ₗ " => Action.Remarkable.OnSet.leftTranslationOnSet law
local notation:70 lhs:70 " •ᵣ " rhs:70 => Action.Remarkable.OnSet.rightTranslationOnSet law rhs lhs
local infix:70 " ••  " => Action.Remarkable.OnSet.conjugationOnSet law

def leftClasses : Set (Set G) := Action.orbit
  (Action.Remarkable.liftToSet (Action.Remarkable.onSelf law)) H
def leftClassesAction : G → leftClasses law H → leftClasses law H :=
  Action.Remarkable.onOrbit law
  (Action.Remarkable.liftToSet (Action.Remarkable.onSelf law)) H
def subgroupAsLeftClass : leftClasses law H := ⟨ H, (Action.memOfSelfOrbit law _ H) ⟩

def rightClasses : Set (Set G) := Action.orbit
  (Action.Remarkable.liftToSet (Action.Remarkable.onSelf (lawᵒᵖ))) H
def rightClassesAction : G → rightClasses law H → rightClasses law H :=
  Action.Remarkable.onOrbit (lawᵒᵖ)
  (Action.Remarkable.liftToSet (Action.Remarkable.onSelf (lawᵒᵖ))) H
def subgroupAsRightClass : rightClasses law H := ⟨ H, (Action.memOfSelfOrbit (lawᵒᵖ) _ H) ⟩

theorem leftClassesOnOp : leftClasses (lawᵒᵖ) H = rightClasses law H := rfl
theorem rightClassesOnOp : rightClasses (lawᵒᵖ) H = leftClasses law H := rfl

theorem leftClassIff (P : Set G) : P ∈ leftClasses law H ↔ ∃ g : G, P = g •ₗ H :=
by
  have p₀ : ∀ {p q : Prop}, (p = q) → (p ↔ q)
  by intro p q h; rw [h]; simp
  apply p₀
  rfl

theorem rightClassIff (P : Set G) : P ∈ rightClasses law H ↔ ∃ g : G, P = H •ᵣ g :=
by
  have p₀ : ∀ {p q : Prop}, (p = q) → (p ↔ q)
  by intro p q h; rw [h]; simp
  apply p₀
  rfl

theorem leftClassMemIff {P : Set G} (PIn : P ∈ leftClasses law H)
  {g : G} (gIn : g ∈ P) (g' : G) : g' ∈ P ↔ ∃ h, h ∈ H ∧ g' = g * h :=
by
  rw [PIn.2]
  rw [PIn.2] at gIn
  have p₀ : ∃ h, h ∈ H ∧ g = PIn.1 * h from gIn
  apply Iff.intro
  exact λ h => have p₁ : ∃ h, h ∈ H ∧ g' = PIn.1 * h from h
    match p₀, p₁ with
    | ⟨ h₀, ⟨ h₀Mem, p₀ ⟩ ⟩, ⟨ h₁, ⟨ h₁Mem, p₁ ⟩ ⟩ => ⟨ (h₀⁻¹ * h₁),
        And.intro (sg.mulMem (sg.invMem h₀Mem) h₁Mem) (by rw [p₀, p₁]; simp) ⟩
  exact λ p₁ => match p₀, p₁ with
    | ⟨ h₀, ⟨ h₀Mem, p₀ ⟩ ⟩, ⟨ h₁, ⟨ h₁Mem, p₁ ⟩ ⟩ => ⟨ h₀ * h₁,
        ⟨ (sg.mulMem h₀Mem h₁Mem), (by rw [p₁, p₀, assoc]; rfl) ⟩ ⟩

theorem rightClassMemIff {P : Set G} (PIn : P ∈ rightClasses law H)
  {g : G} (gIn : g ∈ P) (g' : G) : g' ∈ P ↔ ∃ h, h ∈ H ∧ g' = h * g :=
leftClassMemIff (lawᵒᵖ) H PIn gIn g'

def leftClassOf (g : G) : leftClasses law H :=
  leftClassesAction law H g ⟨ H, Action.memOfSelfOrbit law _ H ⟩
def rightClassOf (g : G) : rightClasses law H :=
  rightClassesAction law H g ⟨ H, Action.memOfSelfOrbit (lawᵒᵖ) _ H ⟩

theorem memOfLeftClassOf (g : G) : g ∈ leftClassOf law H g :=
⟨ one, ⟨ oneMem, (grp.oneNeutralRight g).symm ⟩ ⟩
theorem memOfRightClassOf (g : G) : g ∈ rightClassOf law H g :=
⟨ one, ⟨ oneMem, (grp.oneNeutralLeft g).symm ⟩ ⟩

theorem subgroupStabilizer :
  Action.stabilizer (leftClassesAction law H) (subgroupAsLeftClass law H) = H :=
by
  funext x
  apply propext
  apply Iff.intro
  focus
    intro h
    rw [← show _ = H x from (congrFun <| congrArg Subtype.val h) x]
    apply ⟨ one, ⟨ (sg.oneMem), (grp.oneNeutralRight x).symm ⟩ ⟩
  focus
    intro h
    apply Subtype.eq
    funext y
    apply propext
    suffices p : (∃ h₀, h₀ ∈ H ∧ y = x * h₀) ↔ y ∈ H
    by exact p
    exact ⟨ (λ h' => match h' with | ⟨ h₀, ⟨ h₀In, h' ⟩ ⟩ => h' ▸ sg.mulMem h h₀In),
      λ h' => ⟨ (x⁻¹ * y), ⟨ sg.mulMem (sg.invMem h) h', by simp ⟩ ⟩ ⟩

end

end Subgroup

end Group
