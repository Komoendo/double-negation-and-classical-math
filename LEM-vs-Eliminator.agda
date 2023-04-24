
module LEM-vs-Eliminator where

open import Agda.Primitive using (Level; Setω; lsuc; lzero; _⊔_)


data ⊥ : Set where

¬_ : {l : Level} → Set l → Set l
¬ A = A → ⊥

¬¬_ : {l : Level} → Set l → Set l
¬¬ A = ¬ (¬ A)

explode : {l : Level} {A : Set l} → ⊥ → A
explode = λ ()

data Dec {p} (P : Set p) : Set p where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P


LEM : Setω
LEM = {l : Level} (P : Set l) → Dec P

Double-negation-elimination : Setω
Double-negation-elimination = {l : Level} {P : Set l} → ¬¬ P → P

Eliminator : Setω
Eliminator = {l : Level} → (({A : Set l} → ¬¬ A → A) → ⊥) → ⊥

Powerful-eliminator : Setω
Powerful-eliminator = (({l : Level} {A : Set l} → ¬¬ A → A) → ⊥) → ⊥


-- Double-negation-elimination and LEM are equivalent.
LEM-implies-Double-negation-elimination : LEM → Double-negation-elimination
LEM-implies-Double-negation-elimination lem {l} {P} ¬¬p = f (lem P)
  where
    f : Dec P → P
    f (yes p) = p
    f (no ¬p) = explode (¬¬p ¬p)

Double-negation-elimination-implies-LEM : Double-negation-elimination → LEM
Double-negation-elimination-implies-LEM = λ z P → z (λ z₁ → z₁ (no (λ z₂ → z₁ (yes z₂))))


-- Double negated proposition P proved under Powerful-eliminator = Proposition P that proved under Double-negation-elimination(LEM)
f : {l : Level} {P : Set l} → (Powerful-eliminator → ¬¬ P) → (Double-negation-elimination → P)
f = λ z z₁ → z₁ (z (λ z₂ → z₂ z₁))

g : {l : Level} {P : Set l} → (Double-negation-elimination → P) → (Powerful-eliminator → ¬¬ P)
g = λ z z₁ z₂ → z₁ (λ z₃ → z₂ (z z₃))