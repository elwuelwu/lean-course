/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# Important : the definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes.

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : ¬ true → false :=
begin
  intro h,
  change true → false at h,
  apply h,
  triv,
end

example : false → ¬ true :=
begin
  intro h,
  change true → false,
  intro h2,
  exact h,
end

example : ¬ false → true :=
begin
  intro h,
  triv,
end

example : true → ¬ false :=
begin
  intro h,
  by_contra,
  exact h,
end

example : false → ¬ P :=
begin
  intro h,
  by_contra h2,
  exact h,
end

example : P → ¬ P → false :=
begin
  intros hP nPf,
  apply nPf,
  exact hP,
end

example : P → ¬ (¬ P) :=
begin
  intro hP,
  by_contra,
  apply h,
  exact hP,
end

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  intros hPQ hnQ,
  by_contra,
  apply hnQ,
  apply hPQ,
  exact h,
end

example : ¬ ¬ false → false :=
begin
  intro h,
  apply h,
  by_contra,
  exact h,
end

example : ¬ ¬ P → P :=
begin
  intro h,
  by_contra h2,
  apply h,
  exact h2,
end

example : (¬ Q → ¬ P) → (P → Q) :=
begin
  intros hQP hP,
  by_contra h2,
  apply hQP,
  {
    exact h2,
  },
  {
    exact hP,
  }
end