/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/

variables (P Q R S : Prop)

example : P ↔ P :=
begin
  refl,
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  intro hPQ,
  split,
  {
    intro hQ,
    rw hPQ,
    assumption,
  },
  {
    rw hPQ,
    intro hP,
    assumption,
  },
end

example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split,
  {
    intro hPQ,
    rw hPQ,
  },
  {
    intro hQP,
    rw hQP,
  }
end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intros h1 h2,
  rw h1,
  exact h2,
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  split;
  { rintro ⟨h1, h2⟩,
    exact ⟨h2, h1⟩,}
end

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  split,
  {
    rintros ⟨⟨h11, h22⟩, h2⟩,
    split,
    {
      assumption,
    },
    {
      split;
      assumption,
    }
  },
  {
    rintros ⟨h1, h2, h3⟩,
    split,
    {
      split;
      assumption,
    },
    {
      assumption,
    }
  }
end

example : P ↔ (P ∧ true) :=
begin
  split,
  intro h,
  split,
  {
    assumption,
  },
  {
    triv,
  },
  {
    rintros ⟨hP, ht⟩,
    exact hP,
  },

end

example : false ↔ (P ∧ false) :=
begin
  split,
  {
    intro hf,
    split,
    {exfalso,
    assumption},
    {
      assumption,
    },
  },{
    rintros ⟨hP, hf⟩,
    exact hf,
  }
end

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
begin
  intros hPQ hRS,
  split,
  {
    rintros ⟨hP, hR⟩,
    split,
    {
      rw ← hPQ,
      assumption,
    },
    {
      rwa ← hRS,
    },
  },
  {
    rintro ⟨hQ, hS⟩,
    split,
    {
      rwa hPQ,
    },
    {
      rwa hRS,
    },
  }
end

example : ¬ (P ↔ ¬ P) :=
begin
  intro h,
  have hnP : ¬ P,
  {
    cases h with h1 h2,
    intro hX,
    apply h1,
    assumption,
    assumption,
  },
  apply hnP,
  rwa h,
end
