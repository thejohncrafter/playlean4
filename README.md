
# Some tests on Lean 4

This repo just contains some code that I am writing to play with Lean 4
(hence the name).

I'm currently working on groups. I already defined group quotients, and defined some tools
for group actions along the way. Now I'd like to move on to some basic finite group theory,
maybe Lagrange's theorem.

I have made some design choices that diverge from Lean 3's mathlib that I'd like
to share with the Lean community, hopefully you'll find some ideas interesting.

## Design choices

Most of the desing choices were motivated by the fact that when I have a group,
I want to chose the name of its law, for two reasons :
 * I didn't want to instantiate Groups for both _addition_ and _multiplication_.
   I prefer to have the same structure for both, and relegate the ``addition or
   multiplication'' choice to just a choice of notation.

   Basically, I just want the way I write math in Lean closer to the way I write
   math on a piece of paper : I may just write `let ⟨ G, ⬝ ⟩ be a group`.

   (This is also motivated by my unconditionnal love of esoteric group law symbols :
   `⬝` `∙` `⋆` `★` `▵` `¤`; or even `◫`, `¢`, `¥` or `Æ` when I'm in the mood.)
 * I could want at some point to have two grop laws on the same objecs.
   For instance, this happens for the set of paths on a topological group :
   we have the usual composition, and we also have the group law of
   `[0, 1] → G` which is given by the per-coordinate product.

I can also extend this argument : I might want to have different symbols for different
actions, and so on.

### Algebraic structures

For now, the base class is `Magma` :

```lean
structure Magma where
  carrier : Type
  law : carrier → carrier → carrier
```

This allows me to specify _both_ the carrier and the law when I quantify over groups.

Then I have a `group` typeclass :

```lean
/- Actually, we need a bit of setup before writing this,
   but we'll discuss this afterwards -/

class Group where
  neutral : G
  assoc : ∀ g₁ g₂ g₃ : G, (g₁ * g₂) * g₃ = g₁ * (g₂ * g₃)
  oneNeutralRight : ∀ g : G, g * neutral = g
  invertible : ∀ g : G, ∃ g' : G, g * g' = neutral

```

I didn't need to specify the neutral element directly in the `Magma` structure,
because the neutral is unique and preserved by substructures in groups.
If I were writing about monoids, I would need something like a `PointedMagma`
because the neutral element isn't that well-behaved :

```lean
structure PointedMagma where
  carrier : Type
  law : carrier → carrier → carrier
  distinguished : carrier
```

More generally, I think that it would be interesting to define the concrete type
of algebraic structures not by the type of their carrier like in the Lean 3 mathlib,
but by structures that reflect the language of the algebraic structures that we are
studying.

I think that (but I didn't actually test this idea at the time of writing) this
approach works well with the formalization of category theory : for instance the type
of the objects of the category `Grp` would be
  `Σ (⟨ G, law ⟩ : Magma), Group ⟨ G, law ⟩`.
My gut feeling is that this will behave well, but this is only _a priori_.

### Notation

The benefit of this approach is that whenever I introduce a group, I can choose
the symbol of its law :

```lean
section

variable {G : Magma} [h : Group G]

local infixl:70 " * " => G.law -- (Actually there's a bit more to do, see below...)

-- Lots of lovely theory ♥

end
```

In the current state of the repo, there are some hard truths that come with this :
 * I actually use this only to denote my law by `*` (I also tested `+` at the
   end of the file, but I didn't have anything to write about abelian groups
   at the moment).
 * Because I'm not on latest, I can't denote the neutral element by `1`, and I have
   to use this hack :
   ```lean
   local notation "one" => h.one' -- HACK
   ```
   This will be solved as soon as `nat_lit` will make its way into the release
   channels, but I just have to acknowledge that I have done this to be fair
   with those who will read my code.

#### We need a workaround

There is [an issue](https://github.com/leanprover/lean4/issues/465) with Lean's
pretty printer that makes notations a bit difficult to work with. At the current state,
I have to perform a small workaround :

```lean
local infixl:70 " * " => id Magma.law G
@[appUnexpander id] def unexpandMul : Lean.PrettyPrinter.Unexpander
  | `(id Magma.law G $x $y) => `($x * $y)
  | _ => throw ()
```

This didn't cause any trouble (for the moment), and as soon as the issue will be fixed
I'll just have to remove the extra `id` and the `appUnexpander`, and all will work
Just Fine™.

### Coercion

I am very impressed that Lean survived what I have done to it with coercion.

Joke aside, I have already used a lot of coercion in this repo.

The first trick is to coerce `Magma` to carrier :
```lean
instance CoeCarrier (G : Magma) : CoeSort Magma Type where
  coe m := m.carrier
```

As I have defined cosets (which I call `left classes` and `right classes` here,
I hope this is not an inconvenience), I wanted to define the _type_ of cosets and
to quantify over both them, and over the elements of any given class (coset).

The types of left and right conjugation classes (is this what Bourbaki calls them ?)
are defined as subtypes of `G → Prop`. I wanted to have a _type_ for left classes
because my current goal is to define the quotient group as a group over the left
classes (just like it's done in unergraduate degrees when embedding group theory
in set theory).

```lean
variable {G : Magma} [Group G] (H : Subgroup G)

-- [...]

def isLeftClass (p : G → Prop) := ∃ g, p = λ g' : G => ∃ h : H, g' = (g : G) * (h : G)
def leftClass := Subtype (λ p : G → Prop => isLeftClass H p)
-- Right classes are symetrically defined
```

(By the way, I can't tell wether the `∃ g, p = …` trick is a hack or an actual
good idea, and I'll welcome any argument for or against it.)

With this definition, I can quantify over left classes : `∀ c : leftClass H, …`.

Then, when I have a `leftClass`, I want to coerce it again to `Type` in order to
quantify over its elements. Here is the definition I use to do that :
```lean
instance leftClassCoe (c : leftClass H) : CoeDep (leftClass H) c Type where
  coe := Subtype c.val
```

### Opposite groups

I wanted to have opposite groups (which allow me to prove theorems only on left
class and then to dualize to right classes).
```lean
def op (G : Magma) [Group G] : Magma := ⟨ G, λ g₁ g₂ => G.law g₂ g₁ ⟩
notation G "ᵒᵖ" => op G
```

Writing this down both like cheating and owning mathematics, and I can't tell
if this kind of trick is just a hack or would actually be relevant in matlib.
This time again, any feedback is welcome !

#### Fun with simp

Without much detail, I have this theorem that is obvious in theory, that sounds
hard to proove in Lean if not plainly false, and that is proven by `rfl` :
```lean
theorem rightClassOnOp' : rightClass H = leftClass H.op := rfl
```

### Hack (?) : `simp` as a strategy for free groups

I realized that I could add some simp lemmas to automatically reduce expressions
in groups :
 * `g * g⁻¹ = 1` and `g⁻¹ * g = one`; and the usual neutrality of `one`,
   compatibility with inverse, compatibility with morphisms and the like
 * Hack #1 : `g₁ * (g₂ * g₃) = g₁ * g₂ * g₃`, which I call `normalizeAssoc`
   because it just removes all parenthesis
 * Hack #2 : `g₀ * g * g⁻¹` and `g₀ * g⁻¹ * g = g₀` which automatically
   reduce expressionc like `g * h * h⁻¹ * k` (wich is actually `((g * h) * h⁻¹) * k`
   because in the source `*` is define left-associative.

## Conclusion / Postface / Afterthought

I hope that the Lean community will find some of the ideas that I discussed here
interesting. In other, more hopeful words, I would love to see this repo have
a positive influence over the conversion effort for `mathlib 3 → mathlib 4`.
