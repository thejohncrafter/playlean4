
import Playlean4.Group.Basic

namespace Group

section

variable (G : Type) (law : G → G → G) [grp : Group G law] (H : Set G)

local infixl:70 " * " => id' law
@[appUnexpander id'] def subgroup.unexpandMul : Lean.PrettyPrinter.Unexpander
  | `(id' law G $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => grp.one' -- HACK
local notation g"⁻¹" => grp.inv g

class Subgroup where
  oneMem : one ∈ H
  mulMem : ∀ {g}, g ∈ H → ∀ {g'}, g' ∈ H → g * g' ∈ H
  invMem : ∀ {g}, g ∈ H → (g⁻¹) ∈ H

end

namespace Subgroup

variable {G : Type} (law : G → G → G) [grp : Group G law]

local infixl:70 " * " => id' law
@[appUnexpander id'] def unexpandGMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => grp.one' -- HACK
local notation g"⁻¹" => grp.inv g

def subgroupLaw (H : Set G) [Subgroup G law H] : H → H → H :=
  λ g g' => ⟨ (g : G) * (g' : G), mulMem g.2 g'.2 ⟩

instance GroupOfSubgroup (H : Set G) [Subgroup G law H] : Group H (subgroupLaw law H) where
  one' := ⟨ one, oneMem ⟩
  assoc := λ g g' g'' => Subtype.eq <| grp.assoc g.val g'.val g''.val
  oneNeutralRight := λ g => Subtype.eq <| grp.oneNeutralRight g.val
  invertible := λ g => ⟨ ⟨ (g.val)⁻¹, invMem g.2 ⟩, Subtype.eq <| invCancelRight (g.val : G) ⟩

section -- "variable" doesn't work here for some reason

theorem lemma₁ {H : G → Prop}
  (inhabited : ∃ g : G, g ∈ H)
  (mulInvStable : ∀ {g}, g ∈ H → ∀ {g'}, g' ∈ H → g * g'⁻¹ ∈ H) : one ∈ H :=
match inhabited with
  | ⟨ g, h ⟩ => invCancelRight g ▸ mulInvStable h h

theorem lemma₂ {H : G → Prop}
  (inhabited : ∃ g : G, g ∈ H)
  (mulInvStable : ∀ {g}, g ∈ H → ∀ {g'}, g' ∈ H → g * g'⁻¹ ∈ H) :
    ∀ {g}, g ∈ H → g⁻¹ ∈ H := λ {g} hg =>
oneNeutralLeft (g⁻¹) ▸ mulInvStable (lemma₁ law inhabited mulInvStable) hg

theorem lemma₃ {H : G → Prop}
  (inhabited : ∃ g : G, g ∈ H)
  (mulInvStable : ∀ {g : G}, g ∈ H → ∀ {g' : G}, g' ∈ H → g * g'⁻¹ ∈ H) :
    ∀ {g}, g ∈ H → ∀ {g'}, g' ∈ H → g * g' ∈ H := λ {g} hg {g'} hg' =>
invInvolutive g' ▸ mulInvStable hg (lemma₂ law inhabited mulInvStable hg')

end

instance ofInhabitedMulInvStable {H : G → Prop}
  (inhabited : ∃ g : G, g ∈ H)
  (mulInvStable : ∀ {g}, g ∈ H → ∀ {g'}, g' ∈ H → g * g'⁻¹ ∈ H) : Subgroup G law H where
  oneMem := lemma₁ law inhabited mulInvStable
  mulMem := lemma₃ law inhabited mulInvStable
  invMem := lemma₂ law inhabited mulInvStable

variable (H : Set G) [sg : Subgroup G law H]

instance opIsSubgroup : Subgroup G (lawᵒᵖ) H where
  oneMem := sg.oneMem
  mulMem := λ {g} hg {g'} hg' => sg.mulMem hg' hg
  invMem := sg.invMem

end Subgroup

end Group
