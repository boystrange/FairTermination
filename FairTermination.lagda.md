# A characterization of fair termination in Agda

```
{-# OPTIONS --guardedness #-}

import Level using (zero)
open import Axiom.ExcludedMiddle using (ExcludedMiddle)
open import Axiom.DoubleNegationElimination using (DoubleNegationElimination)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Empty; Satisfiable; _∪_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
open import Function.Base using (_∘_)

postulate State : Set
postulate _~>_  : Rel State Level.zero

Reduces : State -> Set
Reduces S = Satisfiable (S ~>_)

Stuck : State -> Set
Stuck S = ¬ (Reduces S)

_~>*_ : Rel State Level.zero
_~>*_ = Star _~>_

postulate
  excluded-middle : ExcludedMiddle Level.zero
  double-negation-elimination : DoubleNegationElimination Level.zero

data Run (S : State) : Set
record ∞Run (S : State) : Set where
  coinductive
  field force : Run S
open ∞Run public

data Run S where
  stop : (stuck : Stuck S) -> Run S
  _::_ : ∀{S'} (red : S ~> S') (ρ : ∞Run S') -> Run S

data _∈_ : ∀{S} -> State -> Run S -> Set where
  here : ∀{S} (ρ : Run S) -> S ∈ ρ
  step : ∀{S S' T} (red : S ~> S') (ρ : ∞Run S') (pin : T ∈ ρ .force) -> T ∈ (red :: ρ)

Eventually : (State -> Set) -> ∀{S} -> Run S -> Set
Eventually P ρ = ∃[ S ] S ∈ ρ × P S

Always : (State -> Set) -> ∀{S} -> Run S -> Set
Always P ρ = ∀{S} -> S ∈ ρ -> P S

Finite : ∀{S} -> Run S -> Set
Finite = Eventually Stuck

Infinite : ∀{S} -> Run S -> Set
Infinite = Always Reduces

WeaklyTerminating : State -> Set
WeaklyTerminating S = Σ[ ρ ∈ Run S ] Finite ρ

NonTerminating : State -> Set
NonTerminating S = (ρ : Run S) -> Infinite ρ

Fair : ∀{S} -> Run S -> Set
Fair = Eventually Stuck ∪ Eventually NonTerminating

FairlyTerminating : State -> Set
FairlyTerminating S = (ρ : Run S) (fair : Fair ρ) -> Finite ρ

Specification : State -> Set
Specification S = ∀{S'} -> S ~>* S' -> WeaklyTerminating S'

¬Eventually->Always¬ : (P : State -> Set) -> ∀{S} {ρ : Run S} -> ¬ Eventually P ρ -> Always (¬_ ∘ P) ρ
¬Eventually->Always¬ P {S} nep {T} pin with excluded-middle {P T}
... | yes p = ⊥-elim (nep (_ , pin , p))
... | no np = np

finite->¬infinite : ∀{S} {ρ : Run S} -> Finite ρ -> ¬ Infinite ρ
finite->¬infinite (_ , pin , stuck) inf = stuck (inf pin)

¬finite->infinite : ∀{S} {ρ : Run S} -> ¬ Finite ρ -> Infinite ρ
¬finite->infinite nfin pin = double-negation-elimination (¬Eventually->Always¬ Stuck nfin pin)

wt->¬nt : ∀{S} -> WeaklyTerminating S -> ¬ NonTerminating S
wt->¬nt (ρ , fin) nt = finite->¬infinite fin (nt ρ)

¬wt->nt : ∀{S} -> ¬ WeaklyTerminating S -> NonTerminating S
¬wt->nt nwt ρ pin with excluded-middle {Finite ρ}
... | yes fin = ⊥-elim (nwt (ρ , fin))
... | no nfin = ¬finite->infinite nfin pin

make-run : (S : State) -> ∞Run S
make-run S with excluded-middle {Reduces S}
... | yes (S' , red) = λ where .force -> red :: make-run S'
... | no stuck = λ where .force -> stop stuck

make-fair-run : (S : State) -> Σ[ ρ ∈ Run S ] Fair ρ
make-fair-run S with excluded-middle {WeaklyTerminating S}
... | yes (ρ , fin) = ρ , inj₁ fin
... | no nwt with make-run S .force
... | ρ = ρ , inj₂ (S , here ρ , ¬wt->nt nwt)

::-eventually : (P : State -> Set) -> ∀{S S'} (red : S ~> S') {ρ : ∞Run S'} -> Eventually P (ρ .force) -> Eventually P (red :: ρ)
::-eventually P {S} {S'} red {ρ} (T , pin , p) = T , step red ρ pin , p

::-eventually-stuck : ∀{S S'} (red : S ~> S') {ρ : ∞Run S'} -> Eventually Stuck (ρ .force) -> Eventually Stuck (red :: ρ)
::-eventually-stuck = ::-eventually Stuck

::-eventually-nt : ∀{S S'} (red : S ~> S') {ρ : ∞Run S'} -> Eventually NonTerminating (ρ .force) -> Eventually NonTerminating (red :: ρ)
::-eventually-nt = ::-eventually NonTerminating

::-fair : ∀{S S'} {ρ : ∞Run S'} (red : S ~> S') -> Fair (ρ .force) -> Fair (red :: ρ)
::-fair red (inj₁ fin) = inj₁ (::-eventually-stuck red fin)
::-fair red (inj₂ ent) = inj₂ (::-eventually-nt red ent)

∈-stuck : ∀{S S' T} {red : S ~> S'} {ρ : ∞Run S'} -> Stuck T -> T ∈ (red :: ρ) -> T ∈ ρ .force
∈-stuck {_} {_} {_} {red} stuck (here .(_ :: _)) = ⊥-elim (stuck (_ , red))
∈-stuck _ (step _ _ pin) = pin

~>-ft : ∀{S S'} -> S ~> S' -> FairlyTerminating S -> FairlyTerminating S'
~>-ft red ft ρ fair with ft (red :: λ where .force -> ρ) (::-fair red fair)
... | T , pin , stuck = T , ∈-stuck stuck pin , stuck

~>*-ft : ∀{S S'} -> S ~>* S' -> FairlyTerminating S -> FairlyTerminating S'
~>*-ft ε ft = ft
~>*-ft (red ◅ reds) ft = ~>*-ft reds (~>-ft red ft)

ft->wt : ∀{S} -> FairlyTerminating S -> WeaklyTerminating S
ft->wt {S} ft with make-fair-run S
... | ρ , fair with ft ρ fair
... | fin = ρ , fin

ft->spec : ∀{S} -> FairlyTerminating S -> Specification S
ft->spec ft reds = ft->wt (~>*-ft reds ft)

∈-reductions : ∀{S S'} {ρ : Run S} -> S' ∈ ρ -> S ~>* S'
∈-reductions (here _) = ε
∈-reductions (step red _ pin) = red ◅ ∈-reductions pin

spec->ft : ∀{S} -> Specification S -> FairlyTerminating S
spec->ft spec ρ (inj₁ fin) = fin
spec->ft spec ρ (inj₂ (T , pin , nt)) with spec (∈-reductions pin)
... | wt = ⊥-elim (wt->¬nt wt nt)
```
