variables A B C D : Prop

example : A ∧ (A → B) → B :=
assume ⟨ hA, hAimpB ⟩, hAimpB hA

example : A → ¬ (¬ A ∧ B) :=
assume : A,
  show ¬ (¬ A ∧ B), from
    assume ⟨ hnotA, hB ⟩, show false, from hnotA ‹A› 

open classical

example : ¬ (A ∧ B) → (A → ¬ B) :=
assume : ¬ (A ∧ B),
  show (A → ¬ B), from
    assume : A, show ¬ B, from
      assume : B, show false, from
        ‹¬ (A ∧ B)› ⟨ ‹A› , ‹B› ⟩ 

example (h₁ : A ∨ B) (h₂ : A → C) (h₃ : B → D) : C ∨ D :=
show C ∨ D, from
or.elim h₁
  (assume : A, show C ∨ D, from or.inl (h₂ ‹A›))
  (assume : B, show C ∨ D, from or.inr (h₃ ‹B›))

example (h : ¬ A ∧ ¬ B) : ¬ (A ∨ B) :=
have ¬ A, from h.left,
have ¬ B, from h.right,
show ¬ (A ∨ B), from 
  assume : (A ∨ B), show false, from
  or.elim ‹A ∨ B› (assume : A, (‹¬ A› ‹A›)) (assume : B, (‹¬ B› ‹B›))

example (h: ¬ (A ∨ B)) : (¬ A ∧ ¬ B) :=
have ¬ A, from assume : A, show false, from have (A ∨ B), from or.inl ‹A›, ‹¬ (A ∨ B)› ‹A ∨ B›,
have ¬ B, from assume : B, show false, from have (A ∨ B), from or.inr ‹B›, ‹¬ (A ∨ B)› ‹A ∨ B›,
⟨ ‹¬ A› , ‹¬ B› ⟩ 

example : A ∨ ¬ A := by_contradiction(
assume h: ¬ (A ∨ ¬ A),
have ¬ A, from assume : A, show false, from have (A ∨ ¬ A), from or.inl ‹A›, h ‹A ∨ ¬ A›,
have ¬ ¬ A, from assume : ¬ A, show false, from have (A ∨ ¬ A), from or.inr ‹¬ A›, h ‹A ∨ ¬ A›,
‹¬ ¬ A› ‹¬ A› 
)

example (h: ¬ ¬ A) : A := by_contradiction(assume h1 : ¬ A, h h1) 

example : ¬ (A ↔ ¬ A) :=
assume : (A ↔ ¬ A), show false, from
have ¬ A, from assume : A, show false, from have ¬ A, from iff.elim_left ‹A ↔ ¬ A› ‹A›, ‹¬ A› ‹A›,
have A, from iff.elim_right ‹A ↔ ¬ A› ‹¬ A›,
‹¬ A› ‹A›
/-
  or.elim ‹ A ∨ ¬ A › 
    (assume : A, show false, from (iff.elim_left ‹A ↔ ¬ A› ‹A›) ‹A›)
    (assume : ¬ A, show false, from ‹¬ A› (iff.elim_right ‹A ↔ ¬ A› ‹¬ A›)) 
-/
