/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import solutions.section06quotients.sheet2zmod37

/-!

# Z/37 is a ring

(or an additive abelian group if you only get half way through the sheet)

-/

namespace Zmod

-- We already defined negation but right now it's called `neg`. 
-- Let's set up notation for it so we can call it `-`.

instance : has_neg Zmod37 :=
{ neg := neg }

-- Now we can talk about `-⟦a⟧` and Lean will interpret it as `neg ⟦a⟧`.

-- Let's train the simplifier to push everything into
-- the brackets
@[simp] lemma neg_def (a : ℤ) : -⟦a⟧ = ⟦-a⟧ :=
begin
  refl
end

-- Let's also define notation for zero
instance : has_zero Zmod37 :=
{ zero := ⟦0⟧ }

@[simp] lemma zero_def : (0 : Zmod37) = ⟦0⟧ :=
begin
  refl
end

/-

## Maps X → X → X

We're trying to make `Zmod37` into an additive group; we've defined
the additive unit `0` and additive inverse `-`; we still need to 
define the group law `+` though. The type of `+` will be
`Zmod37 → Zmod37 → Zmod37` and this might look a bit weird, so let
me just spell it out. We usually think of addition as a function
which eats two elements of an additive group `G` and returns another
element. But here what we're going to do is to think of addition
as a function `g + _` which eats *one* element `g` and returns a
function `G → G`, namely the function which adds `g` to its input.
With this way of thinking about it, addition is a function
from `Zmod37` to the type of functions from `Zmod37` to `Zmod37`,
and this latter type is called `Zmod37 → Zmod37`. So, putting
it all together, addition has type `Zmod37 → (Zmod37 → Zmod37)`,
and because `→` is right associative in Lean we can write this
as `Zmod37 → Zmod37 → Zmod37` (indeed, that's what "right associative" means).

-/

-- We define addition using a function in the library called `quotient.map₂`
-- which will descend a term of type `ℤ → ℤ → ℤ` to a term of type
-- `Zmod37 → Zmod37 → Zmod37`. We descend addition on the integers.
-- To make this work (to check it's a "well-defined definition") we need to prove
-- a theorem, hence this starts as a definition and ends up as a proof of a theorem.

def add : Zmod37 → Zmod37 → Zmod37 :=
quotient.map₂ (λ a b, a + b) begin
  -- keep intro-ing, and dsimp the lambdas away
  sorry
end

instance : has_add Zmod37 :=
{ add := add }

@[simp] lemma add_def (a b : ℤ) : ⟦a⟧ + ⟦b⟧ = ⟦a + b⟧ :=
begin
  refl
end

/-

## `quotient.induction_on`

The one thing I've not told you about is a really nice way of 
reducing questions about `Zmod37` to equations about integers.
Sure you can use `surjective_quotient_mk` but there's a much
nicer way; you can do "induction on the terms of the quotient".
Let me do this first one for you, to give you the idea of
how to do these simply.

-/
lemma add_zero (z : Zmod37) : z + 0 = z :=
begin
  -- A question about Zmod37, a type we're in the middle of building
  -- an API for.
  apply quotient.induction_on z, clear z,
  -- Still a question about Zmod37, but now all our variables
  -- are integers,
  intro a,
  -- We just trained the simplifier to do questions like these.
  -- We told it `0 = ⟦0⟧` and `⟦a⟧ + ⟦b⟧ = ⟦a + b⟧`.
  simp,
end

-- I'll give you the first line for this one.
lemma add_comm (y z : Zmod37) : y + z = z + y :=
begin
  apply quotient.induction_on₂ y z, clear y z,
  sorry
end

-- See if you can prove the remaining axioms for an additive abelian group yourself.
-- We name this instance `Zmod.add_comm_group` and we'll use it later on.
instance add_comm_group : add_comm_group Zmod37 :=
{ add := (+),
  zero := 0,
  neg := has_neg.neg,
  add_assoc := begin
    sorry
  end,
  zero_add := begin
    sorry
  end,
  add_zero := add_zero,
  add_left_neg := begin
    sorry
  end,
  add_comm := add_comm }

-- Bonus points: see if you can make it a ring!
-- The rest of this file introduces no new techniques; all it offers
-- you is the satisfaction of proving that ℤ/37ℤ is a ring by yourself.

instance : has_one Zmod37 :=
{ one := ⟦1⟧ }

@[simp] lemma one_def : (1 : Zmod37) = ⟦1⟧ :=
begin
  refl
end

def mul : Zmod37 → Zmod37 → Zmod37 :=
quotient.map₂ (λ x y, x * y) begin
  -- tricky!
  sorry,
end

instance : has_mul Zmod37 :=
{ mul := mul }

@[simp] lemma mul_def (a b : ℤ) : ⟦a⟧ * ⟦b⟧ = ⟦a * b⟧ :=
begin
  refl
end

instance : comm_ring Zmod37 :=
{ 
  mul := (*),
  add := (+),
  mul_assoc := begin
    sorry
  end,
  one := 1,
  one_mul := begin
    sorry
  end,
  mul_one := begin
    sorry
  end,
  left_distrib := begin
    sorry,
  end,
  right_distrib := begin
    sorry,
  end,
  mul_comm := begin
    sorry,
end,
  -- the rest of the ring axioms are the axioms for an additive abelian group,
  -- and we did those already.
  ..Zmod.add_comm_group }
end Zmod