
# Some tests on Lean 4

This repo just contains some code that I am writing to play with Lean 4
(hence the name).

I decided to play with another way of defining the algebraic hierarchy.
The aim is to make algebra more flexible, but for now I can't tell if this approach
really has strongs benefits or if it will lead me into more complication than in
the mathlib approach.

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
 * This may (untested yet) simplify the way to write about more complex structures.
   For instance, in a ring, `+` and `*` both form a monoid, and with this approach
   I become able to use the same lemmas for both these laws (e.g. I don't need `add_assoc` and `mul_assoc`).

   But this may also just move the problem to somewhere else, I wouldn't be surprised to be
   forced at some point to write `add.comm` and `mul.comm` or something the like.
 *  (This is also motivated by my unconditionnal love of esoteric group law symbols :
   `⬝` `∙` `⋆` `★` `▵` `¤`; or even `◫`, `¢`, `¥` or `Æ` when I'm in the mood.)
 * I could want at some point to have two grop laws on the same objecs.
   For instance, this happens for the set of paths on a topological group :
   we have the usual composition, and we also have the group law of
   `[0, 1] → G` which is given by the per-coordinate product.

I can also extend this argument : I might want to have different symbols for different
actions, and so on.

The downside is that I often have to explicitly pass the law of a grop as a parameter when I
use theorems, because Lean can't guess what law I'm actually working with
(see `Group/Action.lean` for instance).

To me, this isn't much of a problem because it is just a way to pay for the flexibility that I wanted,
but I can understand that other users of Lean may not appreciate this.

The approach I use here would be fully justified if it cut a substantial part of Mathlib's complexity.
So far, I think that it has its chances, but I can't be sure without experimenting more.

### Algebraic structures

The difference with mathlib is that, here, the laws of an algebraic object are _not_ part of any typeclass.

When I want to work with a group, I get _both_ a carrier and a law, then I specify that together
they form a group
```lean
variable (G : Type) (law : G → G → G) [grp : Group G law]
```

The `Group` typeclass is defined as follows :

```lean
-- Actually, there is a trick to set up this (we need to define `*` as a notation for `law`)
class Group (G : Type) (law : G → G → G) where
  one' : G -- Name hack
  assoc : ∀ g₁ g₂ g₃ : G, (g₁ * g₂) * g₃ = g₁ * (g₂ * g₃)
  oneNeutralRight : ∀ g : G, g * one' = g
  invertible : ∀ g : G, ∃ g' : G, g * g' = one'
```

I didn't need to specify the neutral element,
because the neutral is unique and preserved by substructures in groups.
If I were writing about monoids, I would need to add a parameter like `neutral`
because the neutral element isn't that well-behaved :

```lean
structure Monoid (M : Type) (law : M → M → M) (neutral : M) where [...]
```

More generally, it looks appealing to me to move all the elements of the language of all
algebraic structures out of the typeclasses.

I think that (but I didn't actually test this idea at the time of writing) this
approach works well with the formalization of category theory : for instance the type
of the objects of the category `Grp` would be
  `Σ (G : Type) (law : G → G → G), Group G law`.
My gut feeling is that this would behave well, but this is only _a priori_.

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

This has of course more actual value than enabling me to write fancy symbols.
The idea is that it makes me able to talk uniformly about _multiplicative_ and _additive_ groups,
unlike in mathlib where one has to define both `mul_group` and `add_group`.

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

### Opposite groups

I wanted to have opposite groups (which allow me to prove theorems only on left
class and then to dualize to right classes).
```lean
def op {G : Type} (law : G → G → G) [grp : Group G law] : G → G → G := λ g₁ g₂ => law g₂ g₁
notation law "ᵒᵖ" => op law
```

The problem I see with this is that I define `op` on the _law_ and not on the _group_.
This makes mathematical sense, but it can also make it more difficult to work with groups
because (as it happened when I was writing about groups) notations can easily become cumbersome.

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

## Results, as of now

The alternate way of working with algebraic objects I use in this repo looks promising
enough, but I am not entierely convinced it is really suitable for matlib.

If you skim through this repository, you'll see places where I had to hack with notations,
and other places where I have to pass a lot of explicit parameters because of my design choices.

I also guess that the fact that I use an approach to algebra that is very close to the set theoretic
approach can lead me into definint objects that are inappropriate in a type theoretic framework.
I'm searching for resources on how to work with algebra in type theory, and I'll update this
repo when I'll find a promising approach.

To make my approach to algebra actually pleasant to work with, I would have to play with the internals of
Lean 4 to provide a better support for handling the objects I use here.

I can't be sure for now that the way of working with algebraic objects that I use now
is entierely relevant, but to be sure I guess I'll have to continue experimenting with
more complex objects until I either find that it is simpler that the mathlib way or
run into a dead end. I can't tell which of the two possibilities is the likeliest.

Of course, any feedback is welcome.

I still hope that the Lean community will find some of the ideas that I discussed here
interesting. In other, more hopeful words, I would love to see this repo have
a positive influence over the conversion effort for `mathlib 3 → mathlib 4`.
