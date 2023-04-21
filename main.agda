
module main where

open import Agda.Primitive using (Level; Setω; lsuc; lzero; _⊔_)

record Σ {l₁ l₂ : Level} (A : Set l₁) (B : A → Set l₂) : Set (l₁ ⊔ l₂) where
  field
    fst : A
    snd : B fst

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

¬_ : {l : Level} → Set l → Set l
¬ A = A → ⊥

¬¬_ : {l : Level} → Set l → Set l
¬¬ A = ¬ (¬ A)

explode : {l : Level} {A : Set l} → ⊥ → A
explode = λ ()


-- You can do double negation elimination freely in double negation monad, but for finite number of types.
-- This corresponds to double negation shifting for finite types.
low-eliminator : {l : Level} {A : Set l} → ¬¬ (¬¬ A → A)
low-eliminator = λ z → z (λ z₁ → explode (z₁ (λ z₂ → z (λ _ → z₂))))



Double-negation-shift : Setω
Double-negation-shift = {l₁ l₂ : Level} {A : Set l₁} {B : A → Set l₂} → ((a : A) → ¬¬ (B a)) → ¬¬ ((a : A) → B a)

-- Using eliminator, you can do double negation elimination freely in double negation monad. For infinite number of types.
Eliminator : Setω
Eliminator = {l : Level} → (({A : Set l} → ¬¬ A → A) → ⊥) → ⊥

Eliminator-s : Setω
Eliminator-s = {l : Level} → (((A : Set l) → ¬¬ A → A) → ⊥) → ⊥

double-negation-shift-implies-eliminator-s : Double-negation-shift → Eliminator-s
double-negation-shift-implies-eliminator-s f {l} = f {lsuc l} {l} λ A → low-eliminator {l} {A}

eliminator-s-implies-eliminator : Eliminator-s → Eliminator
eliminator-s-implies-eliminator = λ z z₁ → z (λ z₂ → z₁ (λ {A} x → (z₂ A x)))

-- Double negation shift and Eliminator is equivalent.
double-negation-shift-implies-eliminator : Double-negation-shift → Eliminator
double-negation-shift-implies-eliminator a = eliminator-s-implies-eliminator (double-negation-shift-implies-eliminator-s a)

eliminator-implies-double-negation-shift : Eliminator → Double-negation-shift
eliminator-implies-double-negation-shift = λ z z₁ z₂ → z (λ z₃ → z₂ (λ a → z₃ (z₁ a)))



-- Axiom of choice
Axiom-of-choice : Setω
Axiom-of-choice = {l₁ l₂ l₃ : Level} {X : Set l₁} {A : X → Set l₂} {P : (x : X) → A x → Set l₃}
  → ((x : X) → ¬ ((a : A x) → P x a → ⊥))
  → ¬ ((g : (x : X) → A x) → ((x : X) → P x (g x)) → ⊥)

axiom-of-choice-implies-double-negation-shift : Axiom-of-choice → Double-negation-shift
axiom-of-choice-implies-double-negation-shift actt {l₁} {l₂} {A} {B} f g = actt {l₁} {l₂} {lzero} {A} {B} {λ _ _ → ⊤} (λ x z → f x (λ z₁ → z z₁ tt)) λ g₁ _ → g g₁

axiom-of-choice-implies-eliminator : Axiom-of-choice → Eliminator
axiom-of-choice-implies-eliminator a = double-negation-shift-implies-eliminator (axiom-of-choice-implies-double-negation-shift a)