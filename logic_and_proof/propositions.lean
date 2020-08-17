variables A B C D P Q R: Prop

example : A ∧ (A → B) → B :=
assume ⟨ hA, hAimpB ⟩, hAimpB hA

example : A → ¬ (¬ A ∧ B) :=
assume : A,
  show ¬ (¬ A ∧ B), from
    assume ⟨ hnotA, hB ⟩, show false, from hnotA ‹A› 

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

example : ¬ (A ↔ ¬ A) :=
assume : (A ↔ ¬ A), show false, from
have ¬ A, from assume : A, show false, from have ¬ A, from iff.elim_left ‹A ↔ ¬ A› ‹A›, ‹¬ A› ‹A›,
have A, from iff.elim_right ‹A ↔ ¬ A› ‹¬ A›,
‹¬ A› ‹A›

open classical
------------------------------------------------------------

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

------------------------------------------------------------

example (h: ¬ A ∨ ¬ B) : ¬ (A ∧ B) :=
or.elim h
  (assume : ¬ A, show ¬ (A ∧ B), from assume h1: (A ∧ B), ‹¬ A› h1.left)
  (assume : ¬ B, show ¬ (A ∧ B), from assume h1: (A ∧ B), ‹¬ B› h1.right) 

example (h: ¬ (A ∧ B)) : ¬ A ∨ ¬ B := by_contradiction(
assume h1: ¬ (¬ A ∨ ¬ B),
have A, from by_contradiction(assume : ¬ A, have h2: ¬ A ∨ ¬ B, from or.inl ‹¬ A›, h1 h2),
have B, from by_contradiction(assume : ¬ B, have h2: ¬ A ∨ ¬ B, from or.inr ‹¬ B›, h1 h2),
h ⟨ ‹A›, ‹B› ⟩
)
------------------------------------------------------------

-- Also known as em A
example : A ∨ ¬ A := by_contradiction(
assume h: ¬ (A ∨ ¬ A),
have ¬ A, from assume : A, show false, from have (A ∨ ¬ A), from or.inl ‹A›, h ‹A ∨ ¬ A›,
have ¬ ¬ A, from assume : ¬ A, show false, from have (A ∨ ¬ A), from or.inr ‹¬ A›, h ‹A ∨ ¬ A›,
‹¬ ¬ A› ‹¬ A› 
)

example (h: ¬ ¬ A) : A := by_contradiction(assume h1 : ¬ A, h h1) 
example (h: A) : ¬ ¬ A := show ¬ ¬ A, from assume : ¬ A, ‹¬ A› ‹A› 

------------------------------------------------------------

example (h: A → B) : ¬ A ∨ B :=
or.elim (em A)
  (assume : A, show ¬ A ∨ B, from or.inr (h ‹A›))
  (assume : ¬ A, show ¬ A ∨ B, from or.inl ‹¬ A›) 

example (h: ¬ A ∨ B) : A → B :=
assume : A, or.elim h
  (assume : ¬ A, show B, from false.elim (‹¬ A› ‹A›))
  (assume : B, ‹B›)

------------------------------------------------------------

example (h: A → B) : ¬ B → ¬ A :=
assume : ¬ B, show ¬ A, from assume : A, ‹¬ B› (h ‹A›)

example (h: ¬ B → ¬ A) : A → B :=
assume : A, or.elim (em B)
  (assume : B, ‹B›)
  (assume : ¬ B, show B, from false.elim ((h ‹¬ B›) ‹A›))

------------------------------------------------------------

example (h: ¬ P → (Q ∨ R)) (h1: ¬ Q) (h2: ¬ R) : P :=
or.elim (em P)
  (assume : P, ‹P›)
  (assume : ¬ P, show P, from false.elim
    (or.elim (h ‹¬ P›) (assume : Q, h1 ‹Q›) (assume : R, h2 ‹R›)))

example : A → ((A ∧ B) ∨ (A ∧ ¬ B)) :=
assume : A, or.elim (em B)
  (assume : B, show ((A ∧ B) ∨ (A ∧ ¬ B)), from or.inl ⟨‹A›,‹B›⟩)
  (assume : ¬ B, show ((A ∧ B) ∨ (A ∧ ¬ B)), from or.inr ⟨‹A›,‹¬ B›⟩)





