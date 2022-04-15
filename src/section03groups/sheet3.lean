/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
/-!

# Subgroups

[note: the questions start on line 125 or so! ]

Let's go back to Lean's definition of a group instead of our own.
The reason for this is that Lean's groups API has many many lemmas
about groups.

Let's define our own subgroups though. We start with all the basic
API needed to even get going.

What you need to know: `set G` is the type of subsets of `G`. 
A subgroup of G is a subset of G which is closed under the group
structure (i.e. contains `1` and is closed under `*` and `⁻¹` ).
Here's how we say this in Lean
-/

/-- `mysubgroup G` is the type of subgroups of a group `G`. -/
structure mysubgroup (G : Type) [group G] :=
(carrier : set G) -- `carrier` is the sub*set* of `G` which underlies the subgroup.
-- now the axioms for a subgroup
(one_mem' : (1 : G) ∈ carrier)
(mul_mem' {x y} : x ∈ carrier → y ∈ carrier → x * y ∈ carrier)
(inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier)

/-

These axioms look a little ugly because they're constantly going on
about `carrier`: the subset corresponding to the subgroup. We'll fix
this in the 40 or so lines below. You don't have to worry about these;
this is all the set-up you need to make the definition usable and make
notation like `g ∈ H` work for `H : mysubgroup G`.

## Extensionality

Two subgroups are equal iff they have the same elements!
This lemma is proved in a "formulatic" way (it's true for
subgroups, subrings, subfields etc, with the same proof) 
and the wonderful people at mathlib central wrote some code which 
generates the proof automatically. You run it by tagging
`mysubgroup` with the `@[ext]` attribute:

-/
attribute [ext] mysubgroup

-- we now have theorems `my_subgroup.ext` and `my_subgroup.ext_iff`,
-- plus the `ext` tactic works on subgroups and reduces goals of
-- the form `H₁ = H₂` to `∀ g, g ∈ H₁ ↔ g ∈ H₂`  

-- The next 30 lines are also boilerplate. You can skip them
namespace mysubgroup

-- let G be a group and let G be a subgroup
variables {G : Type} [group G] (H : mysubgroup G)

-- This line makes `g ∈ H` make sense; it says "`g ∈ H` is defined
-- to mean that `g` is in the underlying carrier set"
instance : has_mem G (mysubgroup G) :=
{ mem := λ m H, m ∈ H.carrier }

-- This line means that if `H : subgroup G` and the user suddenly starts
-- talking about `H : set G` without warning, then this just means
-- `H.carrier` again -- the underlying set.
instance : has_coe (mysubgroup G) (set G) := 
{ coe := λ H, H.carrier }


/-- `g` is in `H` considered as a subset of `G`, iff `g` is in `H` considered
as subgroup of `G`. -/
@[simp] lemma mem_coe {g : G} : g ∈ (H : set G) ↔ g ∈ H :=
begin
  -- These two concepts just mean the same thing
  refl
end

-- Now we have some nicer notation we can write a nicer extensionality lemma 
/-- Two subgroups of a group are equal iff they have the same elements. -/
@[ext] def ext' (H K : mysubgroup G) (h : ∀ g : G, g ∈ H ↔ g ∈ K) : H = K :=
begin
  ext x,
  exact h x,
end

-- We now start reformulating the axioms without ever mentioning "carrier".
theorem one_mem : (1 : G) ∈ H :=
begin
  apply H.one_mem',
end

/-- A subgroup is closed under multiplication. -/
theorem mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H :=
begin
  apply H.mul_mem',
end

/-- A subgroup is closed under inverse -/
theorem inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H :=
begin
  apply H.inv_mem',
end

/-

Basic boilerplate code is now over.

So here are the three theorems which you need to remember about subgroups.
Say `H : subgroup G`, and `x` and `y` are terms of type `G` 
(i.e. elements of `G`). Then

`H.one_mem : (1 : G) ∈ H`
`H.mul_mem : x ∈ H → y ∈ H → x * y ∈ H`
`H.inv_mem : x ∈ H → x⁻¹ ∈ H`

These now look like the way a mathematician would write things.

Now let's start to prove basic theorems about subgroups (or, as a the computer
scientists would say, make a basic _interface_ or _API_ for subgroups),
using this sensible notation.

Here's an example; let's prove `x ∈ H ↔ x⁻¹ ∈ H`. Let's put the more
complicated expression on the left hand side of the `↔` though, because then
we can make it a `simp` lemma.

-/

@[simp] theorem inv_mem_iff {x : G} : x⁻¹ ∈ H ↔ x ∈ H := 
begin
  split,
  {
    intro hx,
    have foo := H.inv_mem hx,
    rwa inv_inv at foo,
  },
  {
    intro hx,
    apply H.inv_mem,
    assumption,
  }
end

-- We could prove a bunch more theorems here. Let's just do two more.

theorem mul_mem_cancel_left {x y : G} (hx : x ∈ H) :
  x * y ∈ H ↔ y ∈ H :=
begin
  split,
  {
    intro hxy,
    have poo := H.inv_mem hx,
    have jee := H.mul_mem poo hxy,
    rw ← mul_assoc at jee,
    simp at jee,
    exact jee,
  },
  {
    intro hy,
    apply H.mul_mem;
    assumption,
  }
end

theorem mul_mem_cancel_right {x y : G} (hx : x ∈ H) :
  y * x ∈ H ↔ y ∈ H :=
begin
  split,
  {
    intro hyx,
    have xinv := H.inv_mem hx,
    have foo := H.mul_mem hyx xinv,
    simp at foo,
    exact foo,
  },
  {
    intro hy,
    apply mul_mem;
    assumption,
  }
end

/-- The predicate saying that G is abelian. -/
def is_abelian (G : Type) [group G] : Prop :=
∀ a b : G, a * b = b * a

-- The ``group`` tactic solves identities in groups, like the
-- ``ring`` tactic does in rings.

/-- `conjugate H g` is the subgroup conjugate `gHg⁻¹` of `H`. -/
def conjugate (H : mysubgroup G) (g : G) : mysubgroup G :=
{ carrier := { a : G | ∃ h ∈ H, a = g * h * g⁻¹ },
  one_mem' := begin 
    --dsimp,
    use 1,
    simp,
    exact H.one_mem,
  end,
  mul_mem' := begin 
    intros x y,
    dsimp,
    intros hx hy,
    cases hx with h_x,
    cases hx_h with h2x,
    cases hy with h_y,
    cases hy_h with h2y,
    use (h_x * h_y),
    split,
    {
      exact H.mul_mem h2x h2y,
    },
    {
      rw [hx_h_h, hy_h_h, ←mul_assoc, ←mul_assoc, ←mul_assoc],
      simp,
    }
  end,
  inv_mem' := begin
    dsimp,
    intros x hx,
    cases hx with h,
    cases hx_h with hh,
    have hinv := H.inv_mem hh,
    use h⁻¹,
    split,
    {
      exact hinv,
    },
    {
      rw hx_h_h,
      simp,
      rw ← mul_assoc,
    }
  end,
}

/-- A subgroup is normal iff it's equal to all its conjugates. -/
def is_normal {G : Type} [group G] (H : mysubgroup G) : Prop :=
∀ g : G, conjugate H g = H

example (h_ab : is_abelian G) (H : mysubgroup G) : is_normal H :=
begin
  intro g,
  ext x,
  split,
  {
    rintros ⟨h, hy⟩,
    cases hy with hh,
    rw h_ab at hy_h,
    rw ← mul_assoc at hy_h,
    rw hy_h,
    simpa,
  },
  {
    intro h,
    use g⁻¹ * x * g,
    split, {
      rw h_ab,
      rw ← mul_assoc,
      simpa,
    }, {
      group,
    },
  }
end

end mysubgroup
