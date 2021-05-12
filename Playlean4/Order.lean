
class Order {α : Type} where
  rel : α → α → Prop
  reflexivity : ∀ x : α, rel x x
  transitivity : ∀ x y z : α, rel x y → rel y z → rel x z
  antisymettricity : ∀ x y : α, rel x y → ¬rel y x
