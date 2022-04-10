/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/

-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.

variables (P Q R S : Prop)

example : P → P ∨ Q :=
begin
  intro hP,
  left,
  assumption,
end

example : Q → P ∨ Q :=
begin
  intro hQ,
  right,
  assumption,
end

example : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  rintros (hP|hQ) hPR hQR,
  {
    apply hPR,
    assumption,
  },
  {
    apply hQR,
    assumption,
  },
end

-- symmetry of `or`
example : P ∨ Q → Q ∨ P :=
begin
  rintros (hP|hQ),
  {
    right,
    assumption,
  },
  {
    left,
    assumption,
  }
end

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  split,
  {
    rintros ((hP|hQ)|hR),
    {
      left,
      assumption,
    },
    {
      right,
      left,
      assumption,
    },
    {
      right,
      right,
      assumption,
    },
  },
  {
    rintros (hP|hQ|hR),
    {
      left,
      left,
      assumption,
    },
    {
      left,
      right,
      assumption,
    },
    {
      right,
      assumption,
    }
  }
end

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  rintros hPR hQS (hP|hQ),
  {
    left,
    apply hPR,
    assumption,
  },
  {
    right,
    apply hQS,
    assumption,
  }
end

example : (P → Q) → P ∨ R → Q ∨ R :=
begin
  rintros hPQ (hP|hR),
  {
    left,
    apply hPQ,
    assumption,
  },
  {
    right,
    assumption,
  }
end

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  rintros hPR hQS,
  split,
  {
    rintros (hP|hQ),
    {
      left,
      rwa ← hPR,
    },
    {
      right,
      rwa ← hQS,
    },
  },
  {
    rintros (hR|hS),
    {
      left,
      rwa hPR,
    },
    {
      right,
      rwa hQS,
    }
  }
end

-- de Morgan's laws
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  split,
  {
    intro hPQ,
    split,
    {
      intro hP,
      apply hPQ,
      left,
      exact hP,
    },
    {
      intro hQ,
      apply hPQ,
      right,
      exact hQ,
    }
  },
  {
    rintros ⟨hP, hQ⟩,
    by_contra,
    cases h with h1 h2,
    {
      apply hP,
      exact h1,
    },
    {
      apply hQ,
      exact h2,
    }
  }
end

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  split,
  {
    intro hPQ,
    by_cases hP : P,
    {
      right,
      intro h,
      apply hPQ,
      exact ⟨hP,h⟩,
    },
    {
      left,
      exact hP,
    }
  },
  {
    rintros (hP|hQ),
    {
      intro h,
      apply hP,
      cases h with hP hQ,
      exact hP,
    },
    {
      rintros ⟨hP,hQ2⟩,
      apply hQ,
      exact hQ2,
    } 
  }
end
