
import Playlean4.Group.Basic

namespace Group

section

variable (G : Magma) [h : Group G] (H : Set G)

local infixl:70 " * " => id' Magma.law G
@[appUnexpander id'] def subgroup.unexpandMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => h.one' -- HACK

class Subgroup where
  oneMem : one ∈ H
  mulMem : ∀ {g}, g ∈ H → ∀ {g'}, g' ∈ H → g * g' ∈ H
  invMem : ∀ {g}, g ∈ H → g⁻¹ ∈ H

end

namespace Subgroup

variable {G : Magma} [h : Group G]

local infixl:70 " * " => id' Magma.law G
@[appUnexpander id'] def unexpandGMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => h.one' -- HACK

def asMagma (H : Set G) [Subgroup G H] : Magma :=
  ⟨ Subtype H, λ g g' => ⟨ (g : G) * (g' : G), mulMem g.2 g'.2 ⟩ ⟩

instance GroupOfSubgroup (H : Set G) [Subgroup G H] : Group (asMagma H) where
  one' := ⟨ one, oneMem ⟩
  assoc := λ g g' g'' => Subtype.eq <| h.assoc g.val g'.val g''.val
  oneNeutralRight := λ g => Subtype.eq <| h.oneNeutralRight g.val
  invertible := λ g => ⟨ ⟨ g.val⁻¹, invMem g.2 ⟩, Subtype.eq <| invCancelRight (g.val : G) ⟩

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
oneNeutralLeft (g⁻¹) ▸ mulInvStable (lemma₁ inhabited mulInvStable) hg

theorem lemma₃ {H : G → Prop}
  (inhabited : ∃ g : G, g ∈ H)
  (mulInvStable : ∀ {g : G}, g ∈ H → ∀ {g' : G}, g' ∈ H → g * g'⁻¹ ∈ H) :
    ∀ {g}, g ∈ H → ∀ {g'}, g' ∈ H → g * g' ∈ H := λ {g} hg {g'} hg' =>
invInvolutive g' ▸ mulInvStable hg (lemma₂ inhabited mulInvStable hg')

end

instance ofInhabitedMulInvStable {H : G → Prop}
  (inhabited : ∃ g : G, g ∈ H)
  (mulInvStable : ∀ {g}, g ∈ H → ∀ {g'}, g' ∈ H → g * g'⁻¹ ∈ H) : Subgroup G H where
  oneMem := lemma₁ inhabited mulInvStable
  mulMem := lemma₃ inhabited mulInvStable
  invMem := lemma₂ inhabited mulInvStable

variable (H : Set G) [sg : Subgroup G H]

def op : Set (Gᵒᵖ) := H

instance opIsSubgroup : Subgroup (Gᵒᵖ) (op H) where
  oneMem := sg.oneMem
  mulMem := λ {g} hg {g'} hg' => sg.mulMem hg' hg
  invMem := sg.invMem

notation H "ᵒᵖ" => op H

end Subgroup

end Group
