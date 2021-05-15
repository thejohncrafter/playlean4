
import Playlean4.Group.Basic
import Playlean4.Group.Subgroup
import Playlean4.Group.Action
import Playlean4.Group.OnSet

namespace Group

namespace Subgroup

variable {G : Magma} [grp : Group G]

local infixl:70 " * " => id' Magma.law G
@[appUnexpander id'] def unexpandGMul' : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => grp.one' -- HACK

section

variable (H : Set G) [sg : Subgroup G H]

local infixl:70 " * " => id' Magma.law H
@[appUnexpander id'] def unexpandHMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law H $x $y) => `($x * $y)
  | _ => throw ()

def leftClasses : Set (Set G) := Action.orbit
  (Action.Remarkable.liftToSet Action.Remarkable.onSelf) H
def leftClassesAction : G → leftClasses H → leftClasses H :=
  Action.Remarkable.onOrbit
  (Action.Remarkable.liftToSet Action.Remarkable.onSelf) H
def subgroupAsLeftClass : leftClasses H := ⟨ H, (Action.memOfSelfOrbit _ H) ⟩

def rightClasses : Set (Set G) := @Action.orbit (Gᵒᵖ) _
  (Action.Remarkable.liftToSet Action.Remarkable.onSelf) (Hᵒᵖ)
def rightClassesAction : G → rightClasses H → rightClasses H :=
  Action.Remarkable.onOrbit
  (Action.Remarkable.liftToSet Action.Remarkable.onSelf) (Hᵒᵖ)
def subgroupAsRightClass : rightClasses H := ⟨ H, (Action.memOfSelfOrbit _ H) ⟩

theorem leftClassesOnOp : leftClasses (Hᵒᵖ) = rightClasses H := rfl
theorem rightClassesOnOp : rightClasses (Hᵒᵖ) = leftClasses H := rfl

theorem leftClassIff (P : Set G) : P ∈ leftClasses H ↔ ∃ g : G, P = g •ₗ H :=
by
  have p₀ : ∀ {p q : Prop}, (p = q) → (p ↔ q)
  by intro p q h; rw [h]; simp
  apply p₀
  rfl

theorem rightClassIff (P : Set G) : P ∈ rightClasses H ↔ ∃ g : G, P = H •ᵣ g :=
by
  have p₀ : ∀ {p q : Prop}, (p = q) → (p ↔ q)
  by intro p q h; rw [h]; simp
  apply p₀
  rfl

theorem leftClassMemIff {P : Set G} (PIn : P ∈ leftClasses H)
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

theorem rightClassMemIff {P : Set G} (PIn : P ∈ rightClasses H)
  {g : G} (gIn : g ∈ P) (g' : G) : g' ∈ P ↔ ∃ h, h ∈ H ∧ g' = h * g :=
leftClassMemIff (Hᵒᵖ) PIn gIn g'

def leftClassOf (g : G) : leftClasses H :=
  leftClassesAction H g ⟨ H, Action.memOfSelfOrbit _ H ⟩
def rightClassOf (g : G) : rightClasses H :=
  rightClassesAction H g ⟨ H, Action.memOfSelfOrbit _ H ⟩

theorem memOfLeftClassOf (g : G) : g ∈ leftClassOf H g :=
⟨ one, ⟨ oneMem, (grp.oneNeutralRight g).symm ⟩ ⟩
theorem memOfRightClassOf (g : G) : g ∈ rightClassOf H g :=
⟨ one, ⟨ oneMem, (grp.oneNeutralLeft g).symm ⟩ ⟩

theorem subgroupStabilizer :
  Action.stabilizer (leftClassesAction H) (subgroupAsLeftClass H) = H :=
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
