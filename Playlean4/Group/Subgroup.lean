
import Playlean4.Group.Basic

namespace Group

section

variable (G : Magma) [h : Group G]

local infixl:70 " * " => id' Magma.law G
@[appUnexpander id'] def subgroup.unexpandMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => h.one' -- HACK

structure Subgroup where
  p : G → Prop
  oneMem : p one
  mulMem : ∀ g g' : Subtype p, p ((g : G) * g')
  invMem : ∀ g : Subtype p, p ((g : G)⁻¹)

end

namespace Subgroup

variable {G : Magma} [h : Group G]

local infixl:70 " * " => id' Magma.law G
@[appUnexpander id'] def unexpandGMul : Lean.PrettyPrinter.Unexpander
  | `(id' Magma.law G $x $y) => `($x * $y)
  | _ => throw ()
local notation "one" => h.one' -- HACK

def coeMagma (H : Subgroup G) : Magma :=
  ⟨ Subtype H.p, λ g g' => ⟨ (g : G) * (g' : G), H.mulMem g g' ⟩ ⟩

instance SubgroupCoeMagma : CoeHead (Subgroup G) Magma where
  coe := coeMagma

instance SubgroupCoeCarrier : CoeSort (Subgroup G) Type where
  coe H := ((H : Magma) : Type)

instance GroupOfSubgroup (H : Subgroup G) : Group H where
  one' := ⟨ one, H.oneMem ⟩
  assoc := λ g g' g'' => Subtype.eq <| h.assoc g.val g'.val g''.val
  oneNeutralRight := λ g => Subtype.eq <| h.oneNeutralRight g.val
  invertible := λ g => ⟨ ⟨ g.val⁻¹, H.invMem g ⟩, Subtype.eq <| invCancelRight (g.val : G) ⟩

section -- "variable" doesn't work here for some reason

theorem lemma₁ {p : G → Prop}
  (inhabited : ∃ g : G, p g)
  (mulInvStable : ∀ {g g' : G}, p g → p g' → p (g * g'⁻¹)) : p one :=
match inhabited with
  | ⟨ g, h ⟩ => invCancelRight g ▸ mulInvStable h h

theorem lemma₂ {p : G → Prop}
  (inhabited : ∃ g : G, p g)
  (mulInvStable : ∀ {g g' : G}, p g → p g' → p (g * g'⁻¹)) :
    ∀ g : Subtype p, p (g⁻¹) := λ g =>
oneNeutralLeft ((g : G)⁻¹) ▸ mulInvStable (lemma₁ inhabited mulInvStable) g.2

theorem lemma₃ {p : G → Prop}
  (inhabited : ∃ g : G, p g)
  (mulInvStable : ∀ {g g' : G}, p g → p g' → p (g * g'⁻¹)) :
    ∀ g g' : Subtype p, p ((g : G) * (g' : G)) := λ g g' =>
invInvolutive g'.1 ▸ mulInvStable g.2 (lemma₂ inhabited mulInvStable g')

end

def ofInhabitedMulInvStable (p : G → Prop)
  (inhabited : ∃ g : G, p g)
  (mulInvStable : ∀ {g g' : G}, p g → p g' → p (g * g'⁻¹)) : Subgroup G where
  p := p
  oneMem := lemma₁ inhabited mulInvStable
  mulMem := lemma₃ inhabited mulInvStable
  invMem := lemma₂ inhabited mulInvStable

variable (H : Subgroup G)

def embedding : Morphism H G where
  f g := g.val
  respectMul' := λ g g' : Subtype H.p => by rfl

instance SubgroupCoe : CoeHead ((H : Magma) : Type) (G : Type) where
  coe := embedding H

def op : Subgroup (Gᵒᵖ) where
  p := H.p
  oneMem := H.oneMem
  mulMem := λ g g' => H.mulMem g' g
  invMem := H.invMem

notation H "ᵒᵖ" => op H

end Subgroup

end Group
